open Guesstimator.Core

let fail message = failwith message

let require_close ?(epsilon = 1e-10) label expected actual =
  if abs_float (expected -. actual) > epsilon then
    fail (Printf.sprintf "%s: expected %.12g, got %.12g" label expected actual)

let require_parameter_close ?epsilon label name parameters expected =
  match List.assoc_opt name parameters with
  | Some actual -> require_close ?epsilon label expected actual
  | None -> fail (Printf.sprintf "%s: missing parameter %s" label name)

let fitted model parameters =
  {
    model;
    parameters;
    rss = 0.0;
    r_squared = 1.0;
    aic = 0.0;
    bic = 0.0;
    degrees_of_freedom = 1;
    observations = 3;
  }

let original_parameters scale fit =
  parameters_in_original_problem_size_scale { problem_size_scale = scale } fit

let test_constant_parameters_are_unchanged () =
  let parameters = original_parameters 4.0 (fitted Constant [ ("constant", 42.0) ]) in
  require_parameter_close "constant" "constant" parameters 42.0

let test_polynomial_coefficients_are_rescaled_by_degree () =
  let parameters =
    original_parameters 4.0
      (fitted (polynomial 1) [ ("intercept", 1.0); ("linear", 8.0) ])
  in
  require_parameter_close "polynomial intercept" "intercept" parameters 1.0;
  require_parameter_close "polynomial linear" "linear" parameters 2.0

let test_logarithmic_intercept_is_shifted () =
  let parameters =
    original_parameters 8.0
      (fitted Logarithmic
         [ ("intercept", 3.0 +. (5.0 *. log 8.0)); ("log_coefficient", 5.0) ])
  in
  require_parameter_close "logarithmic intercept" "intercept" parameters 3.0;
  require_parameter_close "logarithmic coefficient" "log_coefficient" parameters 5.0

let test_power_law_log_coefficient_is_shifted () =
  let parameters =
    original_parameters 10.0
      (fitted PowerLaw
         [
           ("coefficient", 0.0);
           ("log_coefficient", log 7.0 +. (1.5 *. log 10.0));
           ("exponent", 1.5);
         ])
  in
  require_parameter_close "power-law coefficient" "coefficient" parameters 7.0;
  require_parameter_close "power-law log coefficient" "log_coefficient" parameters
    (log 7.0);
  require_parameter_close "power-law exponent" "exponent" parameters 1.5

let test_exponential_rate_is_rescaled () =
  let parameters =
    original_parameters 10.0
      (fitted Exponential
         [ ("coefficient", 4.0); ("log_coefficient", log 4.0); ("rate", 2.5) ])
  in
  require_parameter_close "exponential coefficient" "coefficient" parameters 4.0;
  require_parameter_close "exponential log coefficient" "log_coefficient" parameters
    (log 4.0);
  require_parameter_close "exponential rate" "rate" parameters 0.25

let test_quasi_polynomial_adds_induced_highest_degree_term () =
  let parameters =
    original_parameters 5.0
      (fitted (quasi_polynomial 1) [ ("intercept", 2.0); ("linear_log", 10.0) ])
  in
  require_parameter_close "quasi-polynomial intercept" "intercept" parameters 2.0;
  require_parameter_close "quasi-polynomial induced linear" "linear" parameters
    (-10.0 *. log 5.0 /. 5.0);
  require_parameter_close "quasi-polynomial linear log" "linear_log" parameters 2.0

let () =
  test_constant_parameters_are_unchanged ();
  test_polynomial_coefficients_are_rescaled_by_degree ();
  test_logarithmic_intercept_is_shifted ();
  test_power_law_log_coefficient_is_shifted ();
  test_exponential_rate_is_rescaled ();
  test_quasi_polynomial_adds_induced_highest_degree_term ()
