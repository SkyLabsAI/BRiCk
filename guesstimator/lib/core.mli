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

(** Result of a pairwise model comparison.

    [f_statistic] and [p_value] are present when the comparison can be
    expressed as an extra-sum-of-squares F test: a nested restricted model
    against a richer model with materially lower residual error.
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
  val compute_summaries :
    reference:complexity -> options -> sample list -> (summary list, string) result
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

(** Supplying [samples] lets close same-degree polynomial/quasi-polynomial
    comparisons use a leading-term ratio-stability diagnostic instead of BIC
    alone. *)
val compare_fits : ?alpha:float -> ?samples:sample list -> fit -> fit -> comparison

(** Alias for [compare_fits]; pass the restricted/simpler fit first when using
    it as a nested extra-sum-of-squares test. This is not a classical structural
    break Chow test over separate sample groups. *)
val chow_test : ?alpha:float -> fit -> fit -> comparison

(** [estimate ?include_polynomial_degrees ?include_quasi_polynomial_degrees
    samples] estimates the best model as usual, but also retains any requested
    identifiable polynomial or quasi-polynomial degrees in [estimate.fits].
    Requested degrees that cannot be fitted are ignored. This is useful for
    callers that need to compare a specific degree against the selected model
    even when the normal degree search would prune it. *)
val estimate :
  ?alpha:float ->
  ?include_polynomial_degrees:int list ->
  ?include_quasi_polynomial_degrees:int list ->
  sample list ->
  (estimate, string) result
