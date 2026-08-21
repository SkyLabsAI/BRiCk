(** Estimate algorithmic complexity classes from runtime observations. *)

type complexity =
  | Constant
  | Logarithmic
  | Polynomial of int
      (** Polynomial degree. Degrees must be at least 1. Fitted coefficients are
          reported in [fit.parameters]. *)
  | QuasiPolynomial of int
      (** Quasi-polynomial degree. Degrees must be at least 1. Fitted
          coefficients are reported in [fit.parameters]. *)
  | PowerLaw
  | Exponential

type constant
type logarithmic
type polynomial
type quasi_polynomial
type powerlaw
type exponential

module Model : sig
  type _ t =
  | Constant : constant t
  | Logarithmic : logarithmic t
  | Polynomial : float array -> polynomial t
      (** Polynomial coefficients in ascending degree order. *)
  | QuasiPolynomial : float array -> quasi_polynomial t
      (** Quasi-polynomial coefficients in ascending degree order; only the
          highest-degree term is multiplied by [log n]. *)
  | PowerLaw : powerlaw t
  | Exponential : exponential t

  type any = Model : 'm t -> any
end

(** One observation: [time] measured for a given [problem_size]. *)
type sample = {
  problem_size : float;
  time : float;
}

(** Positive scaling factor used to normalize problem sizes. *)
type sample_normalization = {
  problem_size_scale : float;
}

(** [sample_normalization samples] returns the positive maximum problem size to
    use as a normalization scale. It does not require at least three samples;
    model fitting still enforces that separately. *)
val sample_normalization : sample list -> (sample_normalization, string) result

(** [normalize_samples_with normalization samples] divides every problem size by
    [normalization.problem_size_scale] and leaves [time] unchanged. For samples
    that already satisfy the finite-positive fitting domain, this maps problem
    sizes into [(0, 1]], which is inside [[0, 1]] while preserving log-domain
    safety. A fit produced from normalized samples should be predicted with
    problem sizes normalized by the same scale. *)
val normalize_samples_with : sample_normalization -> sample list -> sample list

(** [normalize_samples samples] computes a normalization from [samples] and
    applies it. [fit] and [estimate] themselves do not normalize implicitly;
    callers that want normalized fitting should call this function first. *)
val normalize_samples : sample list -> (sample list, string) result

type parameter = string * float
(** Named fitted parameter. Nonlinear [PowerLaw] and [Exponential] fits include
    both display-scale ["coefficient"] when representable and the stable
    ["log_coefficient"] used for prediction. *)

type fit = {
  model : complexity;
  parameters : parameter list;
  rss : float;
  r_squared : float;
  aic : float;
  bic : float;
  degrees_of_freedom : int;
  observations : int;
}

(** [parameters_in_original_problem_size_scale normalization fit] converts only
    [fit.parameters] from the normalized problem-size coordinate back to the
    original input problem-size units described by [normalization]. It does not
    change RSS, AIC, BIC, R², or any other model-selection statistic, and it
    expects [fit] to have been produced from samples normalized with the same
    [normalization]. Quasi-polynomial output may include an additional non-log
    highest-degree polynomial parameter induced by this change of variables. *)
val parameters_in_original_problem_size_scale :
  sample_normalization -> fit -> parameter list

(** Statistical and practical policy for within-family model selection.

    [minimum_relative_effect] is the smallest RMS added-component effect of
    interest, relative to RMS observed response variation. It is a declared
    model-selection resolution, not an inferred noise level. *)
type selection_options = {
  alpha : float;
  minimum_relative_effect : float;
}

val default_selection_options : selection_options

(** Validate alpha and resolution ranges. All errors are returned together. *)
val validate_selection_options : selection_options -> (unit, string list) result

type materiality =
  | Materially_supported
  | Practically_equivalent
  | Inconclusive

type practical_evidence = {
  response_variation_scale : float;
  rss_improvement : float;
  relative_effect : float;
  relative_standard_error : float;
  confidence_level : float;
  lower_bound : float;
  upper_bound : float;
  resolution : float;
  materiality : materiality;
}

type practical_assessment =
  | Assessed of practical_evidence
  | Numerically_indistinguishable of {
      rss_improvement : float;
      tolerance : float;
    }
  | Evidence_unavailable of string
  | Not_applicable

(** Result of a pairwise model comparison.

    [f_statistic] and [p_value] are present when the comparison can be
    expressed as an extra-sum-of-squares F test. [significant] retains its
    ordinary p-value meaning. For a one-parameter nested comparison with
    samples, [practical_assessment] separately records whether a model-based
    effect interval is above, below, or overlaps the configured resolution.
    For non-nested models, [winner] is chosen by BIC and the test fields are
    [None], except that close same-degree polynomial/quasi-polynomial
    comparisons may use the ratio-stability diagnostic when samples are
    supplied. *)
type comparison = {
  left : complexity;
  right : complexity;
  winner : complexity;
  f_statistic : float option;
  p_value : float option;
  significant : bool;
  practical_assessment : practical_assessment;
  note : string;
}

type estimate = {
  fits : fit list;
  best : fit;
  comparisons : comparison list;
      (** Pairwise comparisons across retained fits from distinct complexity classes. *)
  within_comparisons : comparison list;
      (** Adjacent-degree comparisons recorded within model families such as
          polynomial and quasi-polynomial. *)
  comparison_losers : fit list;
      (** Deduplicated fits that lost at least one comparison performed while
          selecting or reporting candidates. Models that were fitted but never
          compared are not included. *)
}

module Holdout : sig
  val suspicious_relative_rmse_threshold : float

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
    model : complexity;
    count : int;
    median_relative_rmse : float;
    max_relative_rmse : float;
  }

  type summary = {
    kind : kind;
    reference : complexity;
    total : int;
    reference_count : int;
    threshold : float;
    stable : bool;
    groups : group list;
  }

  val best_fit_relative_rmse : estimate -> sample list -> float
  val best_fit_is_suspicious : estimate -> sample list -> bool

  (** Every holdout training estimate uses the supplied alpha and practical
      model-selection resolution; fold selection never silently falls back to
      defaults. *)
  val compute_summaries :
    ?alpha:float ->
    ?minimum_relative_effect:float ->
    reference:complexity ->
    options ->
    sample list ->
    (summary list, string) result
  val is_unstable : summary list -> bool
  val support : summary -> float
end

val string_of_complexity : complexity -> string

(** Parse the canonical names produced by [string_of_complexity]. *)
val complexity_of_string : string -> complexity option

(** [polynomial degree] constructs a polynomial model descriptor. [fit] rejects
    degrees less than 1 and reports fitted coefficients in [fit.parameters]. *)
val polynomial : int -> complexity

(** [quasi_polynomial degree] constructs a quasi-polynomial model descriptor.
    [fit] rejects degrees less than 1 and reports fitted coefficients in
    [fit.parameters]. *)
val quasi_polynomial : int -> complexity

(** [fit model samples] estimates [model]'s parameters from finite positive
    observations. It returns [Error _] when the model is not identifiable from
    the samples or when fitting would produce non-finite statistics. *)
val fit : complexity -> sample list -> (fit, string) result

(** [predict fit ~problem_size] evaluates a fitted model. [problem_size] should
    be finite and positive; nonlinear models are evaluated from their stored
    log-parameterization to avoid avoidable overflow/underflow. *)
val predict : fit -> problem_size:float -> float

(** Supplying [samples] enables two independent diagnostics: close same-degree
    polynomial/quasi-polynomial comparisons may use leading-term ratio
    stability, and eligible one-parameter nested linear comparisons receive a
    model-based practical-effect assessment. [minimum_relative_effect] is the
    SESOI/resolution for the latter; zero recovers alpha-level F-test promotion.
    Without samples, practical assessment is [Not_applicable]. *)
val compare_fits :
  ?alpha:float ->
  ?minimum_relative_effect:float ->
  ?samples:sample list ->
  fit ->
  fit ->
  comparison

(** Alias for [compare_fits]; pass the restricted/simpler fit first when using
    it as a nested extra-sum-of-squares test. This is not a classical structural
    break Chow test over separate sample groups. *)
val chow_test :
  ?alpha:float -> ?minimum_relative_effect:float -> fit -> fit -> comparison

(** [estimate ?minimum_relative_effect ?include_polynomial_degrees
    ?include_quasi_polynomial_degrees samples] estimates the best model using
    the configured practical resolution for one-parameter polynomial and
    quasi-polynomial promotions. Requested degrees are fitted when identifiable
    but retained in [estimate.fits] only when they pass the same adjacent or
    natural-reference materiality rule; forcing never bypasses eligibility.
    Raw RSS, R-squared, AIC, and BIC remain unchanged. *)
val estimate :
  ?alpha:float ->
  ?minimum_relative_effect:float ->
  ?include_polynomial_degrees:int list ->
  ?include_quasi_polynomial_degrees:int list ->
  sample list ->
  (estimate, string) result
