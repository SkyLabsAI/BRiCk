open Cmdliner
open Guesstimator

module Api = Guesstimator.Api
open Guesstimator.Core

let ( let* ) r f = match r with Ok x -> f x | Error _ as e -> e

let parameter_string parameters =
  parameters
  |> List.map (fun (name, value) -> Printf.sprintf "%s=%.5g" name value)
  |> String.concat ", "

let float_string x = Printf.sprintf "%.5g" x

let f_test_string f_statistic p_value =
  match (f_statistic, p_value) with
  | Some f, Some p -> Printf.sprintf "(F,p)=(%s,%s)" (float_string f) (float_string p)
  | None, None -> "(F,p)=n/a"
  | Some _, None | None, Some _ -> "(F,p)=n/a"

type comparison_printing =
  | Print_comparisons_none
  | Print_comparisons_across
  | Print_comparisons_within
  | Print_comparisons_all

let print_within_comparisons = function
  | Print_comparisons_within | Print_comparisons_all -> true
  | Print_comparisons_none | Print_comparisons_across -> false

let print_across_comparisons = function
  | Print_comparisons_across | Print_comparisons_all -> true
  | Print_comparisons_none | Print_comparisons_within -> false

type fit_row = {
  model : string;
  rss : string;
  r_squared : string;
  aic : string;
  bic : string;
  parameters : string;
}

type fit_widths = {
  model_width : int;
  rss_width : int;
  r_squared_width : int;
  aic_width : int;
  bic_width : int;
}

let fit_row (display : Api.display_fit) =
  let fitted = display.Api.fit in
  {
    model = Api.string_of_complexity fitted.model;
    rss = Printf.sprintf "%.4g" fitted.rss;
    r_squared = Printf.sprintf "%.4f" fitted.r_squared;
    aic = Printf.sprintf "%.3f" fitted.aic;
    bic = Printf.sprintf "%.3f" fitted.bic;
    parameters = parameter_string display.Api.parameters;
  }

let fit_widths rows =
  List.fold_left
    (fun widths row ->
      {
        model_width = max widths.model_width (String.length row.model);
        rss_width = max widths.rss_width (String.length row.rss);
        r_squared_width = max widths.r_squared_width (String.length row.r_squared);
        aic_width = max widths.aic_width (String.length row.aic);
        bic_width = max widths.bic_width (String.length row.bic);
      })
    { model_width = 12; rss_width = 10; r_squared_width = 7; aic_width = 9; bic_width = 9 }
    rows

let print_fit ~widths row =
  Printf.printf "  %-*s  RSS=%*s  R^2=%*s  AIC=%*s  BIC=%*s  %s\n"
    widths.model_width row.model widths.rss_width row.rss widths.r_squared_width
    row.r_squared widths.aic_width row.aic widths.bic_width row.bic row.parameters

type comparison_widths = {
  left_width : int;
  right_width : int;
  winner_width : int;
  f_test_width : int;
}

let comparison_widths comparisons =
  List.fold_left
    (fun widths c ->
      let left = Api.string_of_complexity c.left in
      let right = Api.string_of_complexity c.right in
      let winner = Api.string_of_complexity c.winner in
      let f_test = f_test_string c.f_statistic c.p_value in
      {
        left_width = max widths.left_width (String.length left);
        right_width = max widths.right_width (String.length right);
        winner_width = max widths.winner_width (String.length winner);
        f_test_width = max widths.f_test_width (String.length f_test);
      })
    { left_width = 12; right_width = 12; winner_width = 12; f_test_width = 0 }
    comparisons

let print_comparison ~verbose ~widths c =
  let left = Api.string_of_complexity c.left in
  let right = Api.string_of_complexity c.right in
  let winner = Api.string_of_complexity c.winner in
  let f_test = f_test_string c.f_statistic c.p_value in
  Printf.printf "  %-*s vs %-*s -> %-*s  %-*s significant=%s\n" widths.left_width left
    widths.right_width right widths.winner_width winner widths.f_test_width f_test
    (if c.significant then "yes" else "no");
  if verbose then Printf.printf "    note: %s\n" c.note

let print_comparison_section ~verbose heading comparisons =
  Printf.printf "%s\n" heading;
  match comparisons with
  | [] -> Printf.printf "  (none)\n"
  | _ ->
      let widths = comparison_widths comparisons in
      List.iter (print_comparison ~verbose ~widths) comparisons

let percent_string value = Printf.sprintf "%.1f%%" (100.0 *. value)

let holdout_summary_name (summary : Api.holdout_summary) =
  match summary.Holdout.kind with
  | Holdout.KFold { folds } ->
      Printf.sprintf "Hold-out validation (%d-fold round-robin by problem size)" folds
  | Holdout.Tail { fraction } ->
      Printf.sprintf "Tail hold-out validation (largest %s of problem sizes)"
        (percent_string fraction)

let print_holdout_summary (summary : Api.holdout_summary) =
  Printf.printf "%s:\n" (holdout_summary_name summary);
  Printf.printf "  Stability for %s: %s (%d/%d, threshold %s) %s\n"
    (Api.string_of_complexity summary.Holdout.reference)
    (percent_string (Holdout.support summary)) summary.Holdout.reference_count
    summary.Holdout.total (percent_string summary.Holdout.threshold)
    (if summary.Holdout.stable then "stable" else "unstable");
  Printf.printf "  %-20s %7s %20s %20s\n" "Class" "runs" "median relative RSME"
    "max relative RSME";
  List.iter
    (fun (group : Holdout.group) ->
      Printf.printf "  %-20s %7s %20s %20s\n"
        (Api.string_of_complexity group.Holdout.model)
        (Printf.sprintf "%d/%d" group.Holdout.count summary.Holdout.total)
        (percent_string group.Holdout.median_relative_rmse)
        (percent_string group.Holdout.max_relative_rmse))
    summary.Holdout.groups

let column_count_error row_number actual =
  Printf.sprintf "CSV row %d has %d columns; expected exactly 2" row_number actual

let parse_float_cell row_number column value =
  match float_of_string_opt (String.trim value) with
  | Some value -> Ok value
  | None ->
      Error
        (Printf.sprintf "CSV row %d, column %d is not a number: %S" row_number column value)

let parse_sample row_number = function
  | [ problem_size; time ] ->
      let* problem_size = parse_float_cell row_number 1 problem_size in
      let* time = parse_float_cell row_number 2 time in
      Ok { problem_size; time }
  | row -> Error (column_count_error row_number (List.length row))

let looks_like_sample row = match parse_sample 1 row with Ok _ -> true | Error _ -> false

let parse_samples ~first_row rows =
  let rec loop row_number acc = function
    | [] -> Ok (List.rev acc)
    | row :: rows ->
        let* sample = parse_sample row_number row in
        loop (row_number + 1) (sample :: acc) rows
  in
  loop first_row [] rows

let load_csv file =
  try Ok (Csv.load file) with
  | Csv.Failure (row, column, message) ->
      Error (Printf.sprintf "CSV parse error at row %d, column %d: %s" row column message)
  | Sys_error message -> Error message

let samples_of_csv ?header file =
  let* rows = load_csv file in
  match rows with
  | [] -> Error "CSV file is empty"
  | first :: rest -> (
      let* () =
        if List.length first = 2 then Ok () else Error (column_count_error 1 (List.length first))
      in
      let first_is_sample = looks_like_sample first in
      match header with
      | None ->
          if first_is_sample then
            let* samples = parse_samples ~first_row:1 rows in
            Ok (false, samples)
          else
            let* samples = parse_samples ~first_row:2 rest in
            Ok (true, samples)
      | Some true ->
          if first_is_sample then
            Error
              "--header=true was specified, but CSV row 1 contains two numeric values and looks like data"
          else
            let* samples = parse_samples ~first_row:2 rest in
            Ok (true, samples)
      | Some false ->
          if first_is_sample then
            let* samples = parse_samples ~first_row:1 rows in
            Ok (false, samples)
          else
            Error
              "--header=false was specified, but CSV row 1 does not contain two numeric values" )

let suspicious_rmse_warning = function
  | Some relative_rmse ->
      Printf.sprintf " (WARNING: RSME suspiciously high at %s > 20%%)"
        (percent_string relative_rmse)
  | None -> ""

let holdout_stability_warning = function
  | Some (support, threshold) ->
      Printf.sprintf " (WARNING: holdout stability suspiciously low at %s < %s)"
        (percent_string support) (percent_string threshold)
  | None -> ""

let print_result ~verbose ~print_comparisons ~print_loser_fits ~file ~has_header
    (result : Api.fit_result) =
  let fit_rows = List.map fit_row result.Api.display_fits in
  let loser_fit_rows =
    if print_loser_fits then List.map fit_row result.Api.display_loser_fits else []
  in
  let widths = fit_widths (fit_rows @ loser_fit_rows) in
  Printf.printf "Input: %s\n" file;
  Printf.printf "Header: %s\n" (if has_header then "yes" else "no");
  Printf.printf "Normalized samples: %s\n" (if result.Api.normalized then "yes" else "no");
  Printf.printf "Fit parameter scale: %s\n" result.Api.fit_parameter_scale_description;
  Printf.printf "Observations: %d\n" result.Api.estimate.best.observations;
  Printf.printf "Best by BIC: %s%s%s\n"
    (Api.string_of_complexity result.Api.estimate.best.model)
    (suspicious_rmse_warning result.Api.suspicious_relative_rmse)
    (holdout_stability_warning result.Api.holdout_stability_warning);
  Printf.printf "Fits:\n";
  List.iter (print_fit ~widths) fit_rows;
  if print_loser_fits then (
    Printf.printf "Comparison loser fits (not already listed under Fits):\n";
    match loser_fit_rows with
    | [] -> Printf.printf "  (none)\n"
    | loser_fit_rows -> List.iter (print_fit ~widths) loser_fit_rows );
  if print_within_comparisons print_comparisons then
    print_comparison_section ~verbose
      "Within-class comparisons (nested F test where applicable, otherwise BIC):"
      result.Api.estimate.within_comparisons;
  if print_across_comparisons print_comparisons then
    print_comparison_section ~verbose
      "Across-class comparisons (nested F test where applicable, otherwise BIC):"
      result.Api.estimate.comparisons;
  List.iter print_holdout_summary result.Api.holdout_summaries

let invalid_command_line_exit_code = 102

type holdout_cli_options = {
  holdout : bool;
  holdout_tail : bool;
  holdout_folds : int option;
  holdout_tail_fraction : float option;
  holdout_stability_threshold : float option;
}

let holdout_options_or_exit options =
  let invalid_options =
    [
      ( Option.is_some options.holdout_folds && not options.holdout,
        "--holdout-folds requires --holdout" );
      ( Option.is_some options.holdout_tail_fraction && not options.holdout_tail,
        "--holdout-tail-fraction requires --holdout-tail" );
      ( Option.is_some options.holdout_stability_threshold
        && not (options.holdout || options.holdout_tail),
        "--holdout-stability-threshold requires --holdout or --holdout-tail" );
    ]
    |> List.filter_map (fun (invalid, message) -> if invalid then Some message else None)
  in
  match invalid_options with
  | [] ->
      Api.make_holdout_options options.holdout options.holdout_tail
        (Option.value ~default:5 options.holdout_folds)
        (Option.value ~default:0.25 options.holdout_tail_fraction)
        (Option.value ~default:0.80 options.holdout_stability_threshold)
  | messages ->
      List.iter (Printf.eprintf "guesstimator: %s\n") messages;
      exit invalid_command_line_exit_code

let run_fit holdout_cli_options normalize_samples_enabled fit_parameter_scale verbose
    print_comparisons print_loser_fits header file =
  let holdout_options = holdout_options_or_exit holdout_cli_options in
  let* has_header, raw_samples = samples_of_csv ?header file in
  let* result =
    Api.run_fit ~holdout_options ~normalize_samples:normalize_samples_enabled
      fit_parameter_scale raw_samples
  in
  print_result ~verbose ~print_comparisons ~print_loser_fits ~file ~has_header result;
  Ok ()

let run_assert holdout_cli_options normalize_samples_enabled max_delta_bic expected header file =
  let holdout_options = holdout_options_or_exit holdout_cli_options in
  let* _has_header, raw_samples = samples_of_csv ?header file in
  let* result =
    Api.run_assert ~holdout_options ~normalize_samples:normalize_samples_enabled
      ~max_delta_bic ~expected raw_samples
  in
  match result with
  | Api.Assert_ok -> Ok ()
  | Api.Assert_mismatch -> exit 1
  | Api.Assert_suspicious _ -> exit 100
  | Api.Assert_unstable _ -> exit 101

let file_arg =
  let doc =
    "CSV file containing two columns: problem size and time. Use $(b,-) to read from standard input."
  in
  Arg.(required & pos 0 (some filepath) None & info [] ~docv:"FILE" ~doc)

let assert_file_arg =
  let doc =
    "CSV file containing two columns: problem size and time. Use $(b,-) to read from standard input."
  in
  Arg.(required & pos 1 (some filepath) None & info [] ~docv:"FILE" ~doc)

let complexity_arg =
  let parse string =
    match Api.complexity_of_string string with
    | Some complexity -> Ok complexity
    | None ->
        Error
          (`Msg
            (Printf.sprintf "unknown complexity class: %S; expected one of: %s"
               string Api.complexity_class_names))
  in
  let print formatter complexity =
    Format.pp_print_string formatter (Api.string_of_complexity complexity)
  in
  let doc =
    Printf.sprintf
      "Expected best-fit complexity class. Must be one of: %s. Use a positive integer for $(b,N), for example $(b,polynomial-2)."
      Api.complexity_class_names
  in
  Arg.(required & pos 0 (some (conv (parse, print))) None & info [] ~docv:"CLASS" ~doc)

let header_arg =
  let doc =
    "Force header handling. $(b,true) requires a non-numeric first row and skips it; \
     $(b,false) requires every row to contain two numeric values. If omitted, the first \
     row is treated as a header only when it is not a pair of numbers."
  in
  Arg.(value & opt (some bool) None & info [ "header"; "has-header" ] ~docv:"BOOL" ~absent:"auto" ~doc)

let verbose_arg =
  let doc = "Print rationale notes for printed model comparisons." in
  Arg.(value & flag & info [ "verbose"; "v" ] ~doc)

let normalize_samples_arg =
  let doc =
    "Normalize problem sizes to $(b,(0,1]) before fitting. Enabled by default; \
     pass $(b,--normalize-samples=false) to fit raw problem sizes."
  in
  Arg.(value & opt bool true & info [ "normalize-samples" ] ~docv:"BOOL" ~absent:"true" ~doc)

let fit_parameter_scale_arg =
  let choices =
    [
      ("original", Api.Fit_parameter_scale_original);
      ("normalized", Api.Fit_parameter_scale_normalized);
    ]
  in
  let doc =
    "Scale for parameters printed by $(b,fit): $(b,original) converts parameters \
     back to input problem-size units when sample normalization is enabled, while \
     $(b,normalized) prints the fitted normalized coordinate. Choices: original, normalized."
  in
  Arg.(value & opt (enum choices) Api.Fit_parameter_scale_original
       & info [ "fit-parameter-scale" ] ~docv:"SCALE" ~doc)

let print_comparisons_arg =
  let choices =
    [
      ("none", Print_comparisons_none);
      ("across", Print_comparisons_across);
      ("within", Print_comparisons_within);
      ("all", Print_comparisons_all);
    ]
  in
  let doc =
    "Print model comparisons: $(b,none) prints no comparisons, $(b,across) prints comparisons across distinct complexity classes, $(b,within) prints comparisons within a complexity class such as polynomial degree choices, and $(b,all) prints both."
  in
  Arg.(value & opt (enum choices) Print_comparisons_none
       & info [ "print-comparisons" ] ~docv:"WHICH" ~doc)

let print_loser_fits_arg =
  let doc =
    "Print full fit statistics for compared models that lost at least one selection or reported comparison and are not already listed under Fits. This does not enable comparison output or fit models that were never compared."
  in
  Arg.(value & flag & info [ "print-loser-fits" ] ~doc)

let int_at_least minimum name =
  let parse string =
    match int_of_string_opt string with
    | Some value when value >= minimum -> Ok value
    | Some _ | None ->
        Error (`Msg (Printf.sprintf "%s must be an integer >= %d" name minimum))
  in
  let print formatter value = Format.pp_print_int formatter value in
  Arg.conv (parse, print)

let float_between_exclusive ~lower ~upper name =
  let parse string =
    match float_of_string_opt string with
    | Some value when value > lower && value < upper -> Ok value
    | Some _ | None ->
        Error
          (`Msg
            (Printf.sprintf "%s must be a floating-point value between %.1f and %.1f"
               name lower upper))
  in
  let print formatter value = Format.fprintf formatter "%g" value in
  Arg.conv (parse, print)

let fraction_arg name =
  let parse string =
    match float_of_string_opt string with
    | Some value when value >= 0.0 && value <= 1.0 -> Ok value
    | Some _ | None ->
        Error (`Msg (Printf.sprintf "%s must be a fraction between 0.0 and 1.0" name))
  in
  let print formatter value = Format.fprintf formatter "%g" value in
  Arg.conv (parse, print)

let nonnegative_finite_float_arg name =
  let parse string =
    match float_of_string_opt string with
    | Some value
      when value >= 0.0
           && (match classify_float value with FP_nan | FP_infinite -> false | _ -> true) ->
        Ok value
    | Some _ | None ->
        Error (`Msg (Printf.sprintf "%s must be a finite non-negative number" name))
  in
  let print formatter value = Format.fprintf formatter "%g" value in
  Arg.conv (parse, print)

let max_delta_bic_arg =
  let doc =
    "Maximum BIC delta from the best retained fit for CLASS to be accepted as a \
     near-tie. Set to $(b,0) for strict best-model matching."
  in
  Arg.(value & opt (nonnegative_finite_float_arg "--max-delta-bic") 2.0
       & info [ "max-delta-bic" ] ~docv:"DELTA" ~doc)

let holdout_arg =
  let doc =
    "Run grouped round-robin hold-out validation by problem size and report model-selection stability."
  in
  Arg.(value & flag & info [ "holdout" ] ~doc)

let holdout_tail_arg =
  let doc =
    "Run a tail hold-out validation: train on the smallest problem sizes and test on the largest ones."
  in
  Arg.(value & flag & info [ "holdout-tail" ] ~doc)

let holdout_folds_arg =
  let doc =
    "Number of folds for $(b,--holdout). Defaults to 5. Specifying this option requires $(b,--holdout)."
  in
  Arg.(value & opt (some (int_at_least 2 "--holdout-folds")) None
       & info [ "holdout-folds" ] ~docv:"NUM" ~doc)

let holdout_tail_fraction_arg =
  let doc =
    "Fraction of largest problem sizes to hold out for $(b,--holdout-tail). Defaults to 0.25. Specifying this option requires $(b,--holdout-tail)."
  in
  Arg.(value
       & opt
           (some (float_between_exclusive ~lower:0.0 ~upper:1.0 "--holdout-tail-fraction"))
           None
       & info [ "holdout-tail-fraction" ] ~docv:"FRACTION" ~doc)

let holdout_stability_threshold_arg =
  let doc =
    "Required fraction of hold-out runs that must select the full-data best class (for $(b,fit)) or CLASS (for $(b,assert)) to be considered stable. Defaults to 0.80. Specifying this option requires $(b,--holdout) or $(b,--holdout-tail)."
  in
  Arg.(value & opt (some (fraction_arg "--holdout-stability-threshold")) None
       & info [ "holdout-stability-threshold" ] ~docv:"FRACTION" ~doc)

let holdout_options_arg =
  Term.(
    const
      (fun holdout holdout_tail holdout_folds holdout_tail_fraction
           holdout_stability_threshold ->
        {
          holdout;
          holdout_tail;
          holdout_folds;
          holdout_tail_fraction;
          holdout_stability_threshold;
        })
    $ holdout_arg $ holdout_tail_arg $ holdout_folds_arg $ holdout_tail_fraction_arg
    $ holdout_stability_threshold_arg)

let invalid_command_line_exit =
  Cmd.Exit.info invalid_command_line_exit_code ~doc:"invalid command-line arguments"

let fit_cmd =
  let doc = "fit complexity models to observations" in
  let man =
    [
      `S Manpage.s_description;
      `P
        "$(tname) reads a CSV file containing problem sizes and timings, then fits the \
         observations against several complexity models.";
      `S Manpage.s_examples;
      `Pre
        "guesstimator fit timings.csv\n\
         guesstimator fit --normalize-samples=false timings.csv\n\
         guesstimator fit --fit-parameter-scale=normalized timings.csv\n\
         guesstimator fit --print-loser-fits timings.csv\n\
         guesstimator fit --holdout --print-comparisons=all --verbose timings.csv\n\
         guesstimator fit --header=true timings-with-header.csv\n\
         guesstimator fit --header=false timings-no-header.csv";
    ]
  in
  Cmd.v (Cmd.info "fit" ~doc ~man ~exits:(invalid_command_line_exit :: Cmd.Exit.defaults))
    Term.(const run_fit $ holdout_options_arg $ normalize_samples_arg $ fit_parameter_scale_arg
          $ verbose_arg $ print_comparisons_arg $ print_loser_fits_arg $ header_arg $ file_arg)

let assert_cmd =
  let doc = "assert the best-fit complexity class" in
  let exits =
    Cmd.Exit.info 1 ~doc:"CLASS is not within the allowed BIC delta of the best fit"
    :: Cmd.Exit.info 100
         ~doc:"the best fit is suspicious because relative RSME is greater than 20%"
       :: Cmd.Exit.info 101
            ~doc:"hold-out validation did not reach the stability threshold"
          :: invalid_command_line_exit :: Cmd.Exit.defaults
  in
  let man =
    [
      `S Manpage.s_description;
      `P
        "$(tname) reads a CSV file containing problem sizes and timings, fits the \
         observations against several complexity models, and exits successfully when \
         $(i,CLASS) is the best retained fit or is within $(b,--max-delta-bic) of it. \
         It prints no output for either match or mismatch.";
      `S Manpage.s_examples;
      `Pre
        "guesstimator assert polynomial-2 timings.csv\n\
         guesstimator assert --max-delta-bic=0 polynomial-2 timings.csv\n\
         guesstimator assert --normalize-samples=false polynomial-2 timings.csv\n\
         guesstimator assert --holdout polynomial-2 timings.csv\n\
         guesstimator assert --header=true power-law timings-with-header.csv";
    ]
  in
  Cmd.v (Cmd.info "assert" ~doc ~exits ~man)
    Term.(const run_assert $ holdout_options_arg $ normalize_samples_arg $ max_delta_bic_arg
          $ complexity_arg $ header_arg $ assert_file_arg)

let cmd =
  let doc = "estimate algorithmic complexity from runtime observations" in
  Cmd.group (Cmd.info "guesstimator" ~doc) [ fit_cmd; assert_cmd ]

let () = exit (Cmd.eval_result cmd)
