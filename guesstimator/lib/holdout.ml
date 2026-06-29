module type CORE = sig
  type complexity

  type sample = {
    problem_size : float;
    time : float;
  }

  type fit = {
    model : complexity;
    parameters : (string * float) list;
    rss : float;
    r_squared : float;
    aic : float;
    bic : float;
    degrees_of_freedom : int;
    observations : int;
  }

  type comparison = {
    left : complexity;
    right : complexity;
    winner : complexity;
    f_statistic : float option;
    p_value : float option;
    significant : bool;
    note : string;
  }

  type estimate = {
    fits : fit list;
    best : fit;
    comparisons : comparison list;
    within_comparisons : comparison list;
  }

  val predict : fit -> problem_size:float -> float
  val estimate : ?alpha:float -> sample list -> (estimate, string) result
  val string_of_complexity : complexity -> string
end

module Make (Core : CORE) = struct
  let ( let* ) r f = match r with Ok x -> f x | Error _ as e -> e

  let suspicious_relative_rmse_threshold = 0.20

  type options = {
    holdout : bool;
    holdout_tail : bool;
    holdout_folds : int;
    holdout_tail_fraction : float;
    holdout_stability_threshold : float;
  }

  type kind =
    | KFold of { folds : int }
    | Tail of { fraction : float }

  type group = {
    model : Core.complexity;
    count : int;
    median_relative_rmse : float;
    max_relative_rmse : float;
  }

  type summary = {
    kind : kind;
    reference : Core.complexity;
    total : int;
    reference_count : int;
    threshold : float;
    stable : bool;
    groups : group list;
  }

  let median sorted_values =
    match sorted_values with
    | [] -> 0.0 /. 0.0
    | values ->
        let count = List.length values in
        let values = Array.of_list values in
        if count mod 2 = 1 then values.(count / 2)
        else (values.((count / 2) - 1) +. values.(count / 2)) /. 2.0

  let problem_size_groups samples =
    let sorted =
      List.sort
        (fun (left : Core.sample) (right : Core.sample) ->
          compare left.Core.problem_size right.Core.problem_size)
        samples
    in
    let rec loop current_size current_samples groups = function
      | [] -> (
          match current_size with
          | None -> List.rev groups
          | Some problem_size -> List.rev ((problem_size, List.rev current_samples) :: groups) )
      | sample :: rest -> (
          match current_size with
          | Some problem_size when sample.Core.problem_size = problem_size ->
              loop current_size (sample :: current_samples) groups rest
          | Some problem_size ->
              loop (Some sample.Core.problem_size) [ sample ]
                ((problem_size, List.rev current_samples) :: groups)
                rest
          | None -> loop (Some sample.Core.problem_size) [ sample ] groups rest )
    in
    loop None [] [] sorted

  let flatten_groups groups = groups |> List.map snd |> List.concat

  let kfold_splits ~folds samples =
    let groups = problem_size_groups samples in
    let group_count = List.length groups in
    if group_count < 4 then Error "holdout requires at least four distinct problem sizes"
    else
      let folds = min folds group_count in
      let indexed_groups = List.mapi (fun index group -> (index, group)) groups in
      let split fold =
        let heldout, training =
          List.partition (fun (index, _) -> index mod folds = fold) indexed_groups
        in
        (flatten_groups (List.map snd training), flatten_groups (List.map snd heldout))
      in
      Ok (List.init folds split)

  let tail_split ~fraction samples =
    let groups = problem_size_groups samples in
    let group_count = List.length groups in
    if group_count < 4 then Error "tail holdout requires at least four distinct problem sizes"
    else
      let requested = int_of_float (ceil (fraction *. float_of_int group_count)) in
      let heldout_count = max 1 (min requested (group_count - 3)) in
      let training_count = group_count - heldout_count in
      let training, heldout =
        groups
        |> List.mapi (fun index group -> (index, group))
        |> List.partition (fun (index, _) -> index < training_count)
      in
      Ok [ (flatten_groups (List.map snd training), flatten_groups (List.map snd heldout)) ]

  let relative_rmse fitted samples =
    let sample_count = List.length samples in
    let mean_time =
      List.fold_left (fun total (sample : Core.sample) -> total +. sample.Core.time) 0.0 samples
      /. float_of_int sample_count
    in
    let residual_sum_squares =
      List.fold_left
        (fun total (sample : Core.sample) ->
          let residual =
            sample.Core.time -. Core.predict fitted ~problem_size:sample.Core.problem_size
          in
          total +. (residual *. residual))
        0.0 samples
    in
    sqrt (residual_sum_squares /. float_of_int sample_count) /. mean_time

  let best_fit_relative_rmse result samples = relative_rmse result.Core.best samples

  let best_fit_is_suspicious result samples =
    best_fit_relative_rmse result samples > suspicious_relative_rmse_threshold

  let holdout_relative_rmse fitted heldout_samples = relative_rmse fitted heldout_samples

  let holdout_runs splits =
    let evaluate_split (training, heldout) =
      let* result = Core.estimate ~alpha:0.05 training in
      Ok (result.Core.best.model, holdout_relative_rmse result.Core.best heldout)
    in
    let rec loop acc = function
      | [] -> Ok (List.rev acc)
      | split :: rest ->
          let* run = evaluate_split split in
          loop (run :: acc) rest
    in
    loop [] splits

  let summarize ~kind ~reference ~threshold runs =
    let total = List.length runs in
    let models =
      runs
      |> List.map fst
      |> List.sort_uniq compare
      |> List.sort (fun left right ->
             compare (Core.string_of_complexity left) (Core.string_of_complexity right))
    in
    let group model =
      let rmses =
        runs
        |> List.filter_map (fun (run_model, rmse) ->
               if run_model = model then Some rmse else None)
        |> List.sort compare
      in
      {
        model;
        count = List.length rmses;
        median_relative_rmse = median rmses;
        max_relative_rmse = List.fold_left max neg_infinity rmses;
      }
    in
    let groups = List.map group models in
    let reference_count =
      runs |> List.filter (fun (model, _) -> model = reference) |> List.length
    in
    let support = if total = 0 then 0.0 else float_of_int reference_count /. float_of_int total in
    {
      kind;
      reference;
      total;
      reference_count;
      threshold;
      stable = support >= threshold;
      groups;
    }

  let compute_summaries ~reference options samples =
    let summaries = ref [] in
    let* () =
      if options.holdout then
        let* splits = kfold_splits ~folds:options.holdout_folds samples in
        let* runs = holdout_runs splits in
        summaries :=
          summarize ~kind:(KFold { folds = List.length splits }) ~reference
            ~threshold:options.holdout_stability_threshold runs
          :: !summaries;
        Ok ()
      else Ok ()
    in
    let* () =
      if options.holdout_tail then
        let* splits = tail_split ~fraction:options.holdout_tail_fraction samples in
        let* runs = holdout_runs splits in
        summaries :=
          summarize ~kind:(Tail { fraction = options.holdout_tail_fraction }) ~reference
            ~threshold:options.holdout_stability_threshold runs
          :: !summaries;
        Ok ()
      else Ok ()
    in
    Ok (List.rev !summaries)

  let is_unstable summaries = List.exists (fun summary -> not summary.stable) summaries

  let support summary =
    if summary.total = 0 then 0.0
    else float_of_int summary.reference_count /. float_of_int summary.total
end
