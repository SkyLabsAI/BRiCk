open Guesstimator.Core

let fail message = failwith message
let require condition message = if not condition then fail message

let require_close ?(epsilon = 1e-10) label expected actual =
  if abs_float (expected -. actual) > epsilon then
    fail (Printf.sprintf "%s: expected %.12g, got %.12g" label expected actual)

let samples ?(time_scale = 1.0) ?(offset = 0.0) () =
  List.init 100 (fun index ->
      let base_time = if index mod 2 = 0 then 1.0 else 3.0 in
      {
        problem_size = float_of_int (index + 1);
        time = offset +. (time_scale *. base_time);
      })

let fitted model ~rss ~degrees_of_freedom =
  {
    model;
    parameters = [];
    rss;
    r_squared = 0.0;
    aic = 0.0;
    bic = 0.0;
    degrees_of_freedom;
    observations = 100;
  }

let assessed = function
  | Assessed evidence -> evidence
  | Numerically_indistinguishable _ -> fail "expected assessed evidence, got numerical tie"
  | Evidence_unavailable message -> fail ("expected assessed evidence: " ^ message)
  | Not_applicable -> fail "expected assessed evidence, got not-applicable"

let test_default_options () =
  require_close "default alpha" 0.05 default_selection_options.alpha;
  require_close "default resolution" 1e-6
    default_selection_options.minimum_relative_effect;
  require
    (validate_selection_options default_selection_options = Ok ())
    "default selection options should validate";
  require
    (match
       validate_selection_options
         { default_selection_options with minimum_relative_effect = -1.0 }
     with
    | Error _ -> true
    | Ok () -> false)
    "negative resolution should fail validation";
  require
    (match
       validate_selection_options { default_selection_options with alpha = 1.0 }
     with
    | Error _ -> true
    | Ok () -> false)
    "unit alpha should fail validation";
  require
    (match estimate ~minimum_relative_effect:(-1.0) (samples ()) with
    | Error _ -> true
    | Ok _ -> false)
    "Core.estimate should return an error for an invalid resolution"

let equivalent_comparison ?(time_scale = 1.0) ?(offset = 0.0) () =
  let rss_scale = time_scale *. time_scale in
  let simpler =
    fitted (polynomial 1) ~rss:(1.13e-10 *. rss_scale)
      ~degrees_of_freedom:98
  in
  let richer =
    fitted (polynomial 2) ~rss:(9.7e-11 *. rss_scale)
      ~degrees_of_freedom:97
  in
  compare_fits ~samples:(samples ~time_scale ~offset ()) simpler richer

let test_equivalent_effect_is_reported_separately_from_significance () =
  let comparison = equivalent_comparison () in
  require comparison.significant "fixture should be statistically significant";
  require
    (comparison.winner = polynomial 1)
    "practically equivalent richer model should not win";
  let evidence = assessed comparison.practical_assessment in
  require_close ~epsilon:1e-12 "relative effect" 4e-7 evidence.relative_effect;
  require_close ~epsilon:1e-12 "relative standard error" 1e-7
    evidence.relative_standard_error;
  require (evidence.lower_bound > 1.9e-7) "lower bound should use the F/t critical value";
  require (evidence.upper_bound < 6.1e-7) "upper bound should lie below resolution";
  require
    (evidence.materiality = Practically_equivalent)
    "expected practical equivalence"

let test_zero_resolution_recovers_f_test_winner () =
  let rss_scale = 1.0 in
  let simpler =
    fitted (polynomial 1) ~rss:(1.13e-10 *. rss_scale)
      ~degrees_of_freedom:98
  in
  let richer =
    fitted (polynomial 2) ~rss:(9.7e-11 *. rss_scale)
      ~degrees_of_freedom:97
  in
  let comparison =
    compare_fits ~minimum_relative_effect:0.0 ~samples:(samples ()) simpler richer
  in
  require comparison.significant "zero-resolution fixture should be significant";
  require (comparison.winner = polynomial 2) "zero resolution should select richer";
  require
    ((assessed comparison.practical_assessment).materiality = Materially_supported)
    "zero resolution should classify a significant effect as material"

let test_scaling_and_offset_invariance () =
  let original = assessed (equivalent_comparison ()).practical_assessment in
  let scaled =
    assessed (equivalent_comparison ~time_scale:10.0 ()).practical_assessment
  in
  let offset = assessed (equivalent_comparison ~offset:1000.0 ()).practical_assessment in
  require_close ~epsilon:1e-12 "scaled effect" original.relative_effect
    scaled.relative_effect;
  require_close ~epsilon:1e-12 "scaled lower bound" original.lower_bound
    scaled.lower_bound;
  require_close ~epsilon:1e-12 "offset effect" original.relative_effect
    offset.relative_effect;
  require_close ~epsilon:1e-12 "offset upper bound" original.upper_bound
    offset.upper_bound

let test_material_and_inconclusive_outcomes () =
  let sample_set = samples () in
  let material =
    compare_fits ~samples:sample_set
      (fitted (polynomial 1) ~rss:2.0 ~degrees_of_freedom:98)
      (fitted (polynomial 2) ~rss:1.0 ~degrees_of_freedom:97)
    |> fun comparison -> assessed comparison.practical_assessment
  in
  require (material.materiality = Materially_supported) "expected material effect";
  let inconclusive =
    compare_fits ~samples:sample_set
      (fitted (polynomial 1) ~rss:1.97e-10 ~degrees_of_freedom:98)
      (fitted (polynomial 2) ~rss:9.7e-11 ~degrees_of_freedom:97)
    |> fun comparison -> assessed comparison.practical_assessment
  in
  require
    (inconclusive.materiality = Inconclusive)
    "effect interval centered on the resolution should be inconclusive";
  require (inconclusive.lower_bound < 1e-6) "inconclusive lower bound should cross";
  require (inconclusive.upper_bound > 1e-6) "inconclusive upper bound should cross"

let test_resolution_boundary_is_inconclusive () =
  let initial = assessed (equivalent_comparison ()).practical_assessment in
  let simpler = fitted (polynomial 1) ~rss:1.13e-10 ~degrees_of_freedom:98 in
  let richer = fitted (polynomial 2) ~rss:9.7e-11 ~degrees_of_freedom:97 in
  let boundary =
    compare_fits ~minimum_relative_effect:initial.upper_bound
      ~samples:(samples ()) simpler richer
    |> fun comparison -> assessed comparison.practical_assessment
  in
  require
    (boundary.materiality = Inconclusive)
    "a confidence bound equal to the resolution should be inconclusive"

let test_material_forced_degree_remains_available () =
  let samples =
    [ (1.0, 82.0); (2.0, 17.0); (3.0, 2.0); (4.0, 1.0); (5.0, 2.0);
      (6.0, 17.0); (7.0, 82.0) ]
    |> List.map (fun (problem_size, time) -> { problem_size; time })
  in
  let result =
    match estimate ~include_polynomial_degrees:[ 4 ] samples with
    | Ok result -> result
    | Error message -> fail message
  in
  require
    (List.exists (fun fit -> fit.model = polynomial 4) result.fits)
    "a materially supported forced degree should remain available"

let test_numerical_and_not_applicable_assessments () =
  let linear = fitted (polynomial 1) ~rss:1.0 ~degrees_of_freedom:98 in
  let quadratic = fitted (polynomial 2) ~rss:1.0 ~degrees_of_freedom:97 in
  let numerical = compare_fits ~samples:(samples ()) linear quadratic in
  require
    (match numerical.practical_assessment with
    | Numerically_indistinguishable _ -> true
    | Assessed _ | Evidence_unavailable _ | Not_applicable -> false)
    "equal RSS should be numerically indistinguishable";
  let quasi = { linear with model = quasi_polynomial 1; bic = 1.0 } in
  let non_nested = compare_fits ~samples:(samples ()) linear quasi in
  require
    (non_nested.practical_assessment = Not_applicable)
    "equal-parameter non-nested comparison should not use the resolution interval"

let () =
  test_default_options ();
  test_equivalent_effect_is_reported_separately_from_significance ();
  test_zero_resolution_recovers_f_test_winner ();
  test_scaling_and_offset_invariance ();
  test_material_and_inconclusive_outcomes ();
  test_resolution_boundary_is_inconclusive ();
  test_material_forced_degree_remains_available ();
  test_numerical_and_not_applicable_assessments ()
