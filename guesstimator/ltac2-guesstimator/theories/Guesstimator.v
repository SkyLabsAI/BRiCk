Require Import Ltac2.Ltac2.

(** * Ltac2 Bindings for the Guesstimator library

    See Guesstimator README.md for an explanation of the library.

    The Ltac2 bindings try to mirror the CLI. Consequently, the entry points are
    `run_fit` and `run_assert` and their arguments mirror the options of the
    corresponding CLI subcommands.

 *)

Ltac2 Type api_error := [..].
Ltac2 Type api_error ::= [ ApiErrorString (string) ].

Ltac2 api_error_to_string (error : api_error) : string :=
  match error with
  | ApiErrorString message => message
  | _ => Control.throw (Invalid_argument None)
  end.

Ltac2 Type 'a api_result := [ ApiOk ('a) | ApiError (api_error) ].

Ltac2 Type complexity := [..].
Ltac2 Type complexity ::= [
  | ComplexityConstant
  | ComplexityLogarithmic
  | ComplexityPolynomial (int)
  | ComplexityQuasiPolynomial (int)
  | ComplexityPowerLaw
  | ComplexityExponential
].

Ltac2 Type fit_parameter_scale := [..].
Ltac2 Type fit_parameter_scale ::= [
  | FitParameterScaleOriginal
  | FitParameterScaleNormalized
].

(** Problem-size normalization mode for [run_fit] and [run_assert].
    [Unnormalized] preserves the supplied problem sizes, while [Normalized]
    scales them before fitting. *)
Ltac2 Type normalization := [..].
Ltac2 Type normalization ::= [
  | Unnormalized
  | Normalized
].

Ltac2 Type holdout_kind := [..].
Ltac2 Type holdout_kind ::= [
  | HoldoutKFold (int)
  | HoldoutTail (float)
].

Ltac2 Type problem_size := float.

Ltac2 Type 'data sample := {
  problem_size : problem_size;
  time : 'data;
}.

Ltac2 map_sample f {problem_size; time} := {problem_size; time:=f time}.

Ltac2 Type sample_normalization := {
  problem_size_scale : float;
}.

Ltac2 Type parameter := string * float.

Ltac2 Type fit := {
  model : complexity;
  parameters : parameter list;
  rss : float;
  r_squared : float;
  aic : float;
  bic : float;
  degrees_of_freedom : int;
  observations : int;
}.

Ltac2 Type comparison := {
  left : complexity;
  right : complexity;
  winner : complexity;
  f_statistic : float option;
  p_value : float option;
  significant : bool;
  note : string;
}.

Ltac2 Type estimate := {
  fits : fit list;
  best : fit;
  comparisons : comparison list;
  within_comparisons : comparison list;
}.

Ltac2 Type holdout_options := {
  holdout : bool;
  holdout_tail : bool;
  holdout_folds : int;
  holdout_tail_fraction : float;
  holdout_stability_threshold : float;
}.

(** Configuration for [run_fit].

    - [fit_options_holdout] controls optional hold-out validation.
    - [fit_options_normalization] selects whether problem sizes are normalized
      before fitting.
    - [fit_options_parameter_scale] selects the problem-size scale used for
      displayed parameters. *)
Ltac2 Type fit_options := {
  fit_options_holdout : holdout_options;
  fit_options_normalization : normalization;
  fit_options_parameter_scale : fit_parameter_scale;
}.

(** Configuration for [run_assert].

    - [assert_options_holdout] controls optional hold-out validation.
    - [assert_options_normalization] selects whether problem sizes are
      normalized before fitting.
    - [assert_options_max_delta_bic] is the maximum additive BIC delta allowed
      for the separately supplied expected complexity class.

    The expected complexity class and samples remain separate arguments to
    [run_assert]. *)
Ltac2 Type assert_options := {
  assert_options_holdout : holdout_options;
  assert_options_normalization : normalization;
  assert_options_max_delta_bic : float;
}.

Ltac2 Type holdout_group := {
  holdout_group_model : complexity;
  holdout_group_count : int;
  median_relative_rmse : float;
  max_relative_rmse : float;
}.

Ltac2 Type holdout_summary := {
  holdout_summary_kind : holdout_kind;
  holdout_summary_reference : complexity;
  holdout_summary_total : int;
  holdout_summary_reference_count : int;
  holdout_summary_threshold : float;
  holdout_summary_stable : bool;
  holdout_summary_groups : holdout_group list;
}.

Ltac2 Type display_fit := {
  display_fit_fit : fit;
  display_fit_parameters : parameter list;
}.

(** Abstract representation of [Guesstimator.Api.fit_result]. Use the getters
    below instead of matching on its OCaml record representation. *)
Ltac2 Type fit_result.

Ltac2 Type assert_result := [..].
Ltac2 Type assert_result ::= [
  | AssertOk
  | AssertMismatch
  | AssertSuspicious (float)
  | AssertUnstable (holdout_summary list)
].

Declare ML Module "ltac2-guesstimator.plugin".

(** [float_of_string s] parses [s] as an IEEE-754 double and returns the
    corresponding Ltac2 [float]. This is a convenience helper for constructing
    [sample] values in Ltac2 clients and tests. *)
Ltac2 @ external float_of_string : string -> float :=
  "ltac2_guesstimator" "float_of_string".

Ltac2 @ external float_of_int : int -> float :=
  "ltac2_guesstimator" "float_of_int".

(** Comma-separated description of the complexity classes accepted by
    [complexity_of_string]. Degree-bearing classes are described with [-N], for
    example [polynomial-N]. Takes no parameters. *)
Ltac2 @ external complexity_class_names : string :=
  "ltac2_guesstimator" "complexity_class_names".

(** [string_of_complexity c] returns the canonical command-line spelling of
    complexity [c], for example ["constant"] or ["polynomial-2"]. *)
Ltac2 @ external string_of_complexity : complexity -> string :=
  "ltac2_guesstimator" "string_of_complexity".

(** [complexity_of_string s] parses the canonical complexity spelling [s]. It
    returns [Some c] on success and [None] if [s] is not one of the accepted
    class names. *)
Ltac2 @ external complexity_of_string : string -> complexity option :=
  "ltac2_guesstimator" "complexity_of_string".

(** [make_holdout_options holdout holdout_tail holdout_folds
    holdout_tail_fraction holdout_stability_threshold] builds the hold-out
    settings stored in [fit_options] and [assert_options].

    - [holdout] enables k-fold round-robin hold-out validation.
    - [holdout_tail] enables tail hold-out validation on the largest problem
      sizes.
    - [holdout_folds] is the number of round-robin folds used when [holdout] is
      [true].
    - [holdout_tail_fraction] is the fraction of largest problem sizes held out
      when [holdout_tail] is [true].
    - [holdout_stability_threshold] is the required fraction of hold-out runs
      that must select the reference model before the fit is considered stable. *)
Ltac2 @ external make_holdout_options :
  bool -> bool -> int -> float -> float -> holdout_options :=
  "ltac2_guesstimator" "make_holdout_options".

Local Ltac2 @ external default_holdout_options_internal : holdout_options :=
  "ltac2_guesstimator" "default_holdout_options".

Local Ltac2 @ external default_max_delta_bic_internal : float :=
  "ltac2_guesstimator" "default_max_delta_bic".

(** [default_fit_options] matches the [fit] command's defaults: hold-out
    validation is disabled with 5 folds, a 0.25 tail fraction, and a 0.80
    stability threshold ready if enabled; problem sizes are normalized; and
    parameters are displayed in the original problem-size scale. *)
Ltac2 default_fit_options : fit_options :=
  { fit_options_holdout := default_holdout_options_internal;
    fit_options_normalization := Normalized;
    fit_options_parameter_scale := FitParameterScaleOriginal }.

(** [default_assert_options] matches the [assert] command's defaults. It uses
    the same hold-out and normalization settings as [default_fit_options] and
    accepts an expected model within a BIC delta of 2.0. *)
Ltac2 default_assert_options : assert_options :=
  { assert_options_holdout := default_holdout_options_internal;
    assert_options_normalization := Normalized;
    assert_options_max_delta_bic := default_max_delta_bic_internal }.

(** [run_fit options samples] estimates the complexity class of [samples].

    - [options] bundles hold-out validation, problem-size normalization, and
      the scale used to display fitted parameters.
    - [samples] remains a separate argument containing the observed data, with
      [problem_size] as the input size and [time] as the measured cost.

    The result is [ApiOk fit_result] on success or [ApiError error] if the
    samples are invalid or fitting fails. Use [api_error_to_string] for the
    currently known string error case. The [fit_result] value is abstract; use
    the getters below to inspect it. *)
Ltac2 @ external run_fit :
  fit_options -> float sample list -> fit_result api_result :=
  "ltac2_guesstimator" "run_fit".

(** [run_assert options expected samples] checks whether [samples] are
    compatible with [expected].

    - [options] bundles hold-out validation, problem-size normalization, and
      the maximum BIC delta allowed for [expected].
    - [expected] remains a separate argument naming the complexity class being
      asserted.
    - [samples] remains a separate argument containing the observed data.

    The result is [ApiOk AssertOk] when the assertion succeeds,
    [ApiOk AssertMismatch] when [expected] is outside
    [assert_options_max_delta_bic],
    [ApiOk (AssertSuspicious rmse)] when the best fit has suspicious relative
    RMSE, [ApiOk (AssertUnstable summaries)] when hold-out validation is
    unstable, or [ApiError error] when fitting itself fails. Use
    [api_error_to_string] for the currently known string error case. *)
Ltac2 @ external run_assert :
  assert_options -> complexity -> float sample list -> assert_result api_result :=
  "ltac2_guesstimator" "run_assert".

(** [fit_result_normalized result] returns [true] exactly when [result] was
    produced with [Normalized]. *)
Ltac2 @ external fit_result_normalized : fit_result -> bool :=
  "ltac2_guesstimator" "fit_result_normalized".

(** [fit_result_normalization result] returns the problem-size normalization used
    for [result], or [None] when [result] was produced without normalization. *)
Ltac2 @ external fit_result_normalization : fit_result -> sample_normalization option :=
  "ltac2_guesstimator" "fit_result_normalization".

(** [fit_result_samples result] returns the samples actually fitted. These are
    normalized samples when [fit_result_normalized result] is [true], otherwise
    they are the input samples. *)
Ltac2 @ external fit_result_samples : fit_result -> float sample list :=
  "ltac2_guesstimator" "fit_result_samples".

(** [fit_result_estimate result] returns the complete model-selection estimate,
    including all retained fits, the best fit by BIC, and pairwise comparisons. *)
Ltac2 @ external fit_result_estimate : fit_result -> estimate :=
  "ltac2_guesstimator" "fit_result_estimate".

(** [fit_result_display_fits result] returns the retained fits sorted for
    display, together with parameters converted according to the
    [fit_options_parameter_scale] field passed to [run_fit]. *)
Ltac2 @ external fit_result_display_fits : fit_result -> display_fit list :=
  "ltac2_guesstimator" "fit_result_display_fits".

(** [fit_result_parameter_scale_description result] describes the problem-size
    coordinate scale used for [display_fit_parameters] in
    [fit_result_display_fits result]. *)
Ltac2 @ external fit_result_parameter_scale_description : fit_result -> string :=
  "ltac2_guesstimator" "fit_result_parameter_scale_description".

(** [fit_result_suspicious_relative_rmse result] returns [Some rmse] when the
    best fit's relative RMSE exceeds guesstimator's suspicious-fit threshold, and
    [None] otherwise. *)
Ltac2 @ external fit_result_suspicious_relative_rmse : fit_result -> float option :=
  "ltac2_guesstimator" "fit_result_suspicious_relative_rmse".

(** [fit_result_holdout_stability_warning result] returns [Some (support,
    threshold)] when hold-out validation was enabled and the best model's support
    is below the configured stability [threshold]. It returns [None] when there
    is no hold-out stability warning. *)
Ltac2 @ external fit_result_holdout_stability_warning : fit_result -> (float * float) option :=
  "ltac2_guesstimator" "fit_result_holdout_stability_warning".

(** [fit_result_holdout_summaries result] returns detailed summaries for each
    hold-out validation mode enabled in the [fit_options_holdout] field passed
    to [run_fit]. *)
Ltac2 @ external fit_result_holdout_summaries : fit_result -> holdout_summary list :=
  "ltac2_guesstimator" "fit_result_holdout_summaries".
