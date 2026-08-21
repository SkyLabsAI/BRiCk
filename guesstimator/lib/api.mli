type fit_parameter_scale =
  | Fit_parameter_scale_original
  | Fit_parameter_scale_normalized

(** Statistical alpha and declared practical resolution used consistently by
    full-data selection, assertions, and holdout reruns. *)
type selection_options = Core.selection_options
type holdout_options = Core.Holdout.options
type holdout_summary = Core.Holdout.summary

type display_fit = {
  fit : Core.fit;
  parameters : Core.parameter list;
}

type fit_result = {
  selection_options : selection_options;
  normalized : bool;
  normalization : Core.sample_normalization option;
  samples : Core.sample list;
  estimate : Core.estimate;
  display_fits : display_fit list;
  display_loser_fits : display_fit list;
      (** Compared loser fits that are not already present in [display_fits]. *)
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

val complexity_class_names : string
val string_of_complexity : Core.complexity -> string
val complexity_of_string : string -> Core.complexity option

(** [make_selection_options resolution] uses alpha 0.05 and the supplied
    minimum relative added-component effect. *)
val make_selection_options : float -> selection_options
val make_holdout_options : bool -> bool -> int -> float -> float -> holdout_options

val run_fit :
  selection_options:selection_options ->
  holdout_options:holdout_options ->
  normalize_samples:bool ->
  fit_parameter_scale ->
  Core.sample list ->
  (fit_result, string) result

val run_assert :
  selection_options:selection_options ->
  holdout_options:holdout_options ->
  normalize_samples:bool ->
  max_delta_bic:float ->
  expected:Core.complexity ->
  Core.sample list ->
  (assert_result, string) result
