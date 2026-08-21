open Guesstimator.Core

let fail message = failwith message
let require condition message = if not condition then fail message

let is_finite x =
  match classify_float x with FP_nan | FP_infinite -> false | _ -> true

let require_finite label value =
  require (is_finite value) (Printf.sprintf "%s: expected a finite value, got %.12g" label value)

let require_close ?(epsilon = 1e-8) label expected actual =
  if abs_float (expected -. actual) > epsilon then
    fail
      (Printf.sprintf "%s: expected %.12g, got %.12g" label expected actual)

let require_model label expected model =
  let actual = string_of_complexity model in
  if actual <> expected then
    fail (Printf.sprintf "%s: expected %s, got %s" label expected actual)

let require_parameter_close ?epsilon label name parameters expected =
  match List.assoc_opt name parameters with
  | Some actual -> require_close ?epsilon label expected actual
  | None -> fail (Printf.sprintf "%s: missing parameter %s" label name)

let get = function Ok value -> value | Error message -> fail message

let has_fit model result = List.exists (fun fitted -> fitted.model = model) result.fits

let test_forced_degree_bearing_candidates_cannot_bypass_materiality () =
  let samples =
    List.init 8 (fun index ->
        let n = float_of_int (index + 1) in
        { problem_size = n; time = 1.0 +. (2.0 *. n) })
  in
  let default = get (estimate samples) in
  require (not (has_fit (polynomial 3) default))
    "fixture should normally prune polynomial-3 from retained fits";
  let with_polynomial = get (estimate ~include_polynomial_degrees:[ 3 ] samples) in
  require (not (has_fit (polynomial 3) with_polynomial))
    "forced polynomial-3 should not bypass materiality";
  let with_quasi = get (estimate ~include_quasi_polynomial_degrees:[ 2 ] samples) in
  require (not (has_fit (quasi_polynomial 2) with_quasi))
    "forced quasi-polynomial-2 should not bypass materiality"

let test_fit_stores_quasi_polynomial_degree_and_parameters () =
  let samples =
    [ 2.; 4.; 8.; 16.; 32.; 64. ]
    |> List.map (fun n ->
           { problem_size = n; time = 1.0 +. (2.0 *. n *. log n) })
  in
  let fitted = get (fit (quasi_polynomial 1) samples) in
  require_model "fitted model" "quasi-polynomial-1" fitted.model;
  (match fitted.model with
  | QuasiPolynomial degree -> require (degree = 1) "expected degree-one quasi-polynomial"
  | _ -> fail "expected a quasi-polynomial model");
  require_parameter_close "intercept" "intercept" fitted.parameters 1.0;
  require_parameter_close "linear_log" "linear_log" fitted.parameters 2.0;
  require_close "prediction" (1.0 +. (2.0 *. 128.0 *. log 128.0))
    (predict fitted ~problem_size:128.0)

let test_close_polynomial_comparison_uses_ratio_diagnostic () =
  let samples =
    List.init 7 (fun index ->
        let n = float_of_int (index + 2) in
        {
          problem_size = n;
          time = 10.0 +. (n *. log n) -. (2.5 *. n) +. (0.2 *. sin (0.7 *. n));
        })
  in
  let polynomial_fit = get (fit (polynomial 1) samples) in
  let quasi_polynomial_fit = get (fit (quasi_polynomial 1) samples) in
  require (polynomial_fit.bic < quasi_polynomial_fit.bic)
    "fixture should be slightly better by BIC as a polynomial";
  require
    (abs_float (polynomial_fit.bic -. quasi_polynomial_fit.bic) <= 2.0)
    "fixture should be close enough to require the diagnostic";
  require_model "BIC comparison winner" "polynomial-1"
    (compare_fits polynomial_fit quasi_polynomial_fit).winner;
  require_model "diagnostic comparison winner" "quasi-polynomial-1"
    (compare_fits ~samples polynomial_fit quasi_polynomial_fit).winner

let test_nonlinear_predict_uses_stable_log_parameterization () =
  let increasing_samples =
    List.init 4 (fun index ->
        let n = 1000.0 +. float_of_int index in
        { problem_size = n; time = exp (n -. 1000.0) })
  in
  let increasing_fit = get (fit Exponential increasing_samples) in
  let increasing_prediction = predict increasing_fit ~problem_size:1000.0 in
  require_finite "increasing exponential prediction" increasing_prediction;
  require_close "increasing exponential prediction" 1.0 increasing_prediction;
  let decreasing_samples =
    List.init 5 (fun index ->
        let n = 10000.0 +. float_of_int index in
        { problem_size = n; time = exp (1000.0 -. (0.1 *. n)) })
  in
  let decreasing_fit = get (fit Exponential decreasing_samples) in
  let decreasing_prediction = predict decreasing_fit ~problem_size:10000.0 in
  require_finite "decreasing exponential prediction" decreasing_prediction;
  require_close "decreasing exponential prediction" 1.0 decreasing_prediction

let test_large_polynomial_regression_is_finite () =
  let samples =
    [ 1.; 2.; 3.; 4. ]
    |> List.map (fun multiplier ->
           let problem_size = multiplier *. 1e200 in
           { problem_size; time = multiplier })
  in
  let fitted = get (fit (polynomial 1) samples) in
  require_finite "large polynomial RSS" fitted.rss;
  require_finite "large polynomial BIC" fitted.bic;
  require_close "large polynomial prediction" 2.5
    (predict fitted ~problem_size:(2.5 *. 1e200));
  let quadratic_fit = get (fit (polynomial 2) samples) in
  require_finite "large quadratic polynomial RSS" quadratic_fit.rss;
  require_close "large quadratic polynomial prediction" 2.5
    (predict quadratic_fit ~problem_size:(2.5 *. 1e200))

let test_fitted_polynomial_model_stores_degree_and_parameters () =
  let samples =
    [ 1.; 2.; 3.; 4. ]
    |> List.map (fun n -> { problem_size = n; time = 1.0 +. (2.0 *. n) })
  in
  let fitted = get (fit (polynomial 1) samples) in
  (match fitted.model with
  | Polynomial degree -> require (degree = 1) "expected degree-one polynomial"
  | _ -> fail "expected a polynomial model");
  require_parameter_close "intercept parameter" "intercept" fitted.parameters 1.0;
  require_parameter_close "linear parameter" "linear" fitted.parameters 2.0;
  require_close "prediction from fitted parameters" 21.0 (predict fitted ~problem_size:10.0)

let test_roundoff_tolerance_uses_variation_not_offset () =
  let samples =
    List.init 6 (fun index ->
        let n = float_of_int (index + 1) in
        { problem_size = n; time = 1e12 +. (0.001 *. n *. log n) })
  in
  let constant_fit = get (fit Constant samples) in
  let quasi_fit = get (fit (quasi_polynomial 1) samples) in
  require_model "offset comparison winner" "quasi-polynomial-1"
    (compare_fits ~samples constant_fit quasi_fit).winner

let test_large_f_statistic_has_zero_tail_probability () =
  let restricted =
    {
      model = Constant;
      parameters = [ ("constant", 0.0) ];
      rss = 2.857142857142857e307;
      r_squared = 0.0;
      aic = 0.0;
      bic = 0.0;
      degrees_of_freedom = 9;
      observations = 10;
    }
  in
  let richer =
    {
      model = polynomial 2;
      parameters = [];
      rss = 1.0;
      r_squared = 1.0;
      aic = 0.0;
      bic = 0.0;
      degrees_of_freedom = 7;
      observations = 10;
    }
  in
  let comparison = compare_fits restricted richer in
  require comparison.significant "expected huge finite F statistic to be significant";
  (match comparison.p_value with
  | Some p_value -> require_close "huge F tail probability" 0.0 p_value
  | None -> fail "expected a p-value for nested comparison")

let () =
  test_forced_degree_bearing_candidates_cannot_bypass_materiality ();
  test_fit_stores_quasi_polynomial_degree_and_parameters ();
  test_close_polynomial_comparison_uses_ratio_diagnostic ();
  test_nonlinear_predict_uses_stable_log_parameterization ();
  test_large_polynomial_regression_is_finite ();
  test_fitted_polynomial_model_stores_degree_and_parameters ();
  test_roundoff_tolerance_uses_variation_not_offset ();
  test_large_f_statistic_has_zero_tail_probability ()
