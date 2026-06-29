let ( let* ) r f = match r with Ok x -> f x | Error _ as e -> e

type fit_parameter_scale =
  | Fit_parameter_scale_original
  | Fit_parameter_scale_normalized

type holdout_options = Core.Holdout.options
type holdout_summary = Core.Holdout.summary

type display_fit = {
  fit : Core.fit;
  parameters : Core.parameter list;
}

type fit_result = {
  normalized : bool;
  normalization : Core.sample_normalization option;
  samples : Core.sample list;
  estimate : Core.estimate;
  display_fits : display_fit list;
  fit_parameter_scale_description : string;
  suspicious_relative_rmse : float option;
  holdout_stability_warning : (float * float) option;
  holdout_summaries : holdout_summary list;
}

type assert_result =
  | Assert_ok
  | Assert_mismatch
  | Assert_suspicious of float
  | Assert_unstable of holdout_summary list

let complexity_class_names =
  "constant, logarithmic, polynomial-N, quasi-polynomial-N, power-law, exponential"

let string_of_complexity = Core.string_of_complexity
let complexity_of_string = Core.complexity_of_string

let make_holdout_options holdout holdout_tail holdout_folds holdout_tail_fraction
    holdout_stability_threshold =
  {
    Core.Holdout.holdout;
    holdout_tail;
    holdout_folds;
    holdout_tail_fraction;
    holdout_stability_threshold;
  }

let maybe_normalize_samples enabled samples =
  if enabled then
    let* normalization = Core.sample_normalization samples in
    Ok (Some normalization, Core.normalize_samples_with normalization samples)
  else Ok (None, samples)

let fit_parameter_scale_description ~normalization = function
  | Fit_parameter_scale_original -> (
      match normalization with
      | Some _ -> "original problem size"
      | None -> "input problem size" )
  | Fit_parameter_scale_normalized -> (
      match normalization with
      | Some _ -> "normalized problem size"
      | None -> "fitted coordinate scale" )

let display_parameters ~fit_parameter_scale ~normalization fitted =
  match (fit_parameter_scale, normalization) with
  | Fit_parameter_scale_normalized, _ -> fitted.Core.parameters
  | Fit_parameter_scale_original, Some normalization ->
      Core.parameters_in_original_problem_size_scale normalization fitted
  | Fit_parameter_scale_original, None -> fitted.Core.parameters

let holdout_stability_warning summaries =
  let unstable = List.filter (fun summary -> not summary.Core.Holdout.stable) summaries in
  match unstable with
  | [] -> None
  | first :: rest ->
      let worst =
        List.fold_left
          (fun worst summary ->
            if Core.Holdout.support summary < Core.Holdout.support worst then summary else worst)
          first rest
      in
      Some (Core.Holdout.support worst, worst.Core.Holdout.threshold)

let suspicious_relative_rmse result samples =
  let relative_rmse = Core.Holdout.best_fit_relative_rmse result samples in
  if relative_rmse > Core.Holdout.suspicious_relative_rmse_threshold then
    Some relative_rmse
  else None

let run_fit ~holdout_options ~normalize_samples fit_parameter_scale raw_samples =
  let* normalization, samples = maybe_normalize_samples normalize_samples raw_samples in
  let* estimate = Core.estimate ~alpha:0.05 samples in
  let* holdout_summaries =
    Core.Holdout.compute_summaries ~reference:estimate.Core.best.Core.model
      holdout_options samples
  in
  let parameters = display_parameters ~fit_parameter_scale ~normalization in
  let display_fits =
    estimate.Core.fits
    |> List.sort (fun a b -> compare a.Core.bic b.Core.bic)
    |> List.map (fun fit -> { fit; parameters = parameters fit })
  in
  Ok
    {
      normalized = normalize_samples;
      normalization;
      samples;
      estimate;
      display_fits;
      fit_parameter_scale_description =
        fit_parameter_scale_description ~normalization fit_parameter_scale;
      suspicious_relative_rmse = suspicious_relative_rmse estimate samples;
      holdout_stability_warning = holdout_stability_warning holdout_summaries;
      holdout_summaries;
    }

let included_degrees_for_assert = function
  | Core.Polynomial degree -> ([ degree ], [])
  | Core.QuasiPolynomial degree -> ([], [ degree ])
  | Core.Constant | Core.Logarithmic | Core.PowerLaw | Core.Exponential -> ([], [])

let requested_fit_within_delta ~max_delta_bic expected result =
  match List.find_opt (fun fitted -> fitted.Core.model = expected) result.Core.fits with
  | None -> false
  | Some fitted -> fitted.Core.bic -. result.Core.best.Core.bic <= max_delta_bic

let run_assert ~holdout_options ~normalize_samples ~max_delta_bic ~expected raw_samples =
  let* _normalization, samples = maybe_normalize_samples normalize_samples raw_samples in
  let include_polynomial_degrees, include_quasi_polynomial_degrees =
    included_degrees_for_assert expected
  in
  let* result =
    Core.estimate ~alpha:0.05 ~include_polynomial_degrees
      ~include_quasi_polynomial_degrees samples
  in
  match suspicious_relative_rmse result samples with
  | Some relative_rmse -> Ok (Assert_suspicious relative_rmse)
  | None ->
      if not (requested_fit_within_delta ~max_delta_bic expected result) then
        Ok Assert_mismatch
      else
        let* holdout_summaries =
          Core.Holdout.compute_summaries ~reference:expected holdout_options samples
        in
        if Core.Holdout.is_unstable holdout_summaries then
          Ok (Assert_unstable holdout_summaries)
        else Ok Assert_ok
