open Ltac2_plugin
open Tac2ffi
open Tac2externals

module G = Guesstimator.Core
module Api = Guesstimator.Api

let define name =
  define Tac2expr.{ mltac_plugin = "ltac2_guesstimator"; mltac_tactic = name }

let constructor_names name =
  [
    name;
    "Guesstimator." ^ name;
    "skylabs.guesstimator.Guesstimator." ^ name;
  ]

let locate_constructor name =
  let rec loop = function
    | [] -> CErrors.anomaly (Pp.str ("Ltac2 guesstimator constructor not found: " ^ name))
    | candidate :: candidates -> (
        try Tac2env.locate_constructor (Libnames.qualid_of_string candidate) with
        | Not_found -> loop candidates )
  in
  loop (constructor_names name)

let of_constructor name args = Tac2ffi.of_open (locate_constructor name, args)

let constructor_label value =
  let constructor, args = Tac2ffi.to_open value in
  (Names.Id.to_string (Names.KerName.label constructor), args)

let expect_tuple arity value =
  let fields = Tac2ffi.to_tuple value in
  if Array.length fields = arity then fields else assert false

let of_api_error_string message =
  of_constructor "ApiErrorString" [| Tac2ffi.of_string message |]

let of_api_result of_ok = function
  | Ok value -> Tac2ffi.of_block (0, [| of_ok value |])
  | Error message -> Tac2ffi.of_block (1, [| of_api_error_string message |])

let read_instruction_counter_as_int () =
  match Instr.read_counter () with
  | Error message -> Error message
  | Ok value ->
      if Int64.compare value (Int64.of_int max_int) > 0 then
        Error "instruction count bigger than max_int"
      else Ok (Int64.to_int value)

let to_float value = Float64.to_float (Tac2ffi.to_float value)
let of_float value = Tac2ffi.of_float (Float64.of_float value)

let of_complexity = function
  | G.Constant -> of_constructor "ComplexityConstant" [||]
  | G.Logarithmic -> of_constructor "ComplexityLogarithmic" [||]
  | G.Polynomial degree -> of_constructor "ComplexityPolynomial" [| Tac2ffi.of_int degree |]
  | G.QuasiPolynomial degree ->
      of_constructor "ComplexityQuasiPolynomial" [| Tac2ffi.of_int degree |]
  | G.PowerLaw -> of_constructor "ComplexityPowerLaw" [||]
  | G.Exponential -> of_constructor "ComplexityExponential" [||]

let to_complexity value =
  match constructor_label value with
  | "ComplexityConstant", [||] -> G.Constant
  | "ComplexityLogarithmic", [||] -> G.Logarithmic
  | "ComplexityPolynomial", [| degree |] -> G.Polynomial (Tac2ffi.to_int degree)
  | "ComplexityQuasiPolynomial", [| degree |] -> G.QuasiPolynomial (Tac2ffi.to_int degree)
  | "ComplexityPowerLaw", [||] -> G.PowerLaw
  | "ComplexityExponential", [||] -> G.Exponential
  | _ -> assert false

let to_fit_parameter_scale value =
  match constructor_label value with
  | "FitParameterScaleOriginal", [||] -> Api.Fit_parameter_scale_original
  | "FitParameterScaleNormalized", [||] -> Api.Fit_parameter_scale_normalized
  | _ -> assert false

let to_normalize_samples value =
  match constructor_label value with
  | "Unnormalized", [||] -> false
  | "Normalized", [||] -> true
  | _ -> assert false

let rec of_assert_result = function
  | Api.Assert_ok -> of_constructor "AssertOk" [||]
  | Api.Assert_mismatch -> of_constructor "AssertMismatch" [||]
  | Api.Assert_suspicious relative_rmse ->
      of_constructor "AssertSuspicious" [| of_float relative_rmse |]
  | Api.Assert_unstable summaries ->
      of_constructor "AssertUnstable" [| Tac2ffi.of_list of_holdout_summary summaries |]

and of_holdout_kind = function
  | G.Holdout.KFold { folds } -> of_constructor "HoldoutKFold" [| Tac2ffi.of_int folds |]
  | G.Holdout.Tail { fraction } -> of_constructor "HoldoutTail" [| of_float fraction |]

and to_holdout_kind value =
  match constructor_label value with
  | "HoldoutKFold", [| folds |] -> G.Holdout.KFold { folds = Tac2ffi.to_int folds }
  | "HoldoutTail", [| fraction |] -> G.Holdout.Tail { fraction = to_float fraction }
  | _ -> assert false

and of_sample (sample : G.sample) =
  Tac2ffi.of_tuple [| of_float sample.G.problem_size; of_float sample.G.time |]

and to_sample value : G.sample =
  let fields = expect_tuple 2 value in
  { G.problem_size = to_float fields.(0); time = to_float fields.(1) }

and of_sample_normalization (normalization : G.sample_normalization) =
  Tac2ffi.of_tuple [| of_float normalization.G.problem_size_scale |]

and of_parameter (name, value) = Tac2ffi.of_pair Tac2ffi.of_string of_float (name, value)

and of_fit (fit : G.fit) =
  Tac2ffi.of_tuple
    [|
      of_complexity fit.G.model;
      Tac2ffi.of_list of_parameter fit.G.parameters;
      of_float fit.G.rss;
      of_float fit.G.r_squared;
      of_float fit.G.aic;
      of_float fit.G.bic;
      Tac2ffi.of_int fit.G.degrees_of_freedom;
      Tac2ffi.of_int fit.G.observations;
    |]

and of_comparison (comparison : G.comparison) =
  Tac2ffi.of_tuple
    [|
      of_complexity comparison.G.left;
      of_complexity comparison.G.right;
      of_complexity comparison.G.winner;
      Tac2ffi.of_option of_float comparison.G.f_statistic;
      Tac2ffi.of_option of_float comparison.G.p_value;
      Tac2ffi.of_bool comparison.G.significant;
      Tac2ffi.of_string comparison.G.note;
    |]

and of_estimate (estimate : G.estimate) =
  Tac2ffi.of_tuple
    [|
      Tac2ffi.of_list of_fit estimate.G.fits;
      of_fit estimate.G.best;
      Tac2ffi.of_list of_comparison estimate.G.comparisons;
      Tac2ffi.of_list of_comparison estimate.G.within_comparisons;
    |]

and of_holdout_group (group : G.Holdout.group) =
  Tac2ffi.of_tuple
    [|
      of_complexity group.G.Holdout.model;
      Tac2ffi.of_int group.G.Holdout.count;
      of_float group.G.Holdout.median_relative_rmse;
      of_float group.G.Holdout.max_relative_rmse;
    |]

and of_holdout_summary (summary : G.Holdout.summary) =
  Tac2ffi.of_tuple
    [|
      of_holdout_kind summary.G.Holdout.kind;
      of_complexity summary.G.Holdout.reference;
      Tac2ffi.of_int summary.G.Holdout.total;
      Tac2ffi.of_int summary.G.Holdout.reference_count;
      of_float summary.G.Holdout.threshold;
      Tac2ffi.of_bool summary.G.Holdout.stable;
      Tac2ffi.of_list of_holdout_group summary.G.Holdout.groups;
    |]

and of_holdout_options (options : Api.holdout_options) =
  Tac2ffi.of_tuple
    [|
      Tac2ffi.of_bool options.G.Holdout.holdout;
      Tac2ffi.of_bool options.G.Holdout.holdout_tail;
      Tac2ffi.of_int options.G.Holdout.holdout_folds;
      of_float options.G.Holdout.holdout_tail_fraction;
      of_float options.G.Holdout.holdout_stability_threshold;
    |]

and to_holdout_options value : Api.holdout_options =
  let fields = expect_tuple 5 value in
  {
    G.Holdout.holdout = Tac2ffi.to_bool fields.(0);
    holdout_tail = Tac2ffi.to_bool fields.(1);
    holdout_folds = Tac2ffi.to_int fields.(2);
    holdout_tail_fraction = to_float fields.(3);
    holdout_stability_threshold = to_float fields.(4);
  }

and of_display_fit (display : Api.display_fit) =
  Tac2ffi.of_tuple [| of_fit display.Api.fit; Tac2ffi.of_list of_parameter display.Api.parameters |]

let to_fit_options value =
  let fields = expect_tuple 3 value in
  ( to_holdout_options fields.(0),
    to_normalize_samples fields.(1),
    to_fit_parameter_scale fields.(2) )

let to_assert_options value =
  let fields = expect_tuple 3 value in
  (to_holdout_options fields.(0), to_normalize_samples fields.(1), to_float fields.(2))

let default_holdout_options =
  of_holdout_options (Api.make_holdout_options false false 5 0.25 0.80)

let fit_result_tag : Api.fit_result Tac2dyn.Val.tag = Tac2dyn.Val.create "ltac2_guesstimator.fit_result"
let fit_result = Tac2ffi.repr_ext fit_result_tag

let _ =
  define "float_of_string" (string @-> ret float) @@ fun s ->
  Float64.of_string s

let _ =
  define "float_of_int" (int @-> ret float) @@ fun n ->
  Float64.of_float (Float.of_int n)

let _ =
  define "pp_float" (unit @-> float @-> ret pp) @@ fun () value ->
  Pp.str (Float64.to_string value)

let _ =
  define "instructions_result" (unit @-> ret valexpr) @@ fun () ->
  read_instruction_counter_as_int () |> of_api_result Tac2ffi.of_int

let _ =
  define "instructions" (unit @-> tac int) @@ fun () ->
  match read_instruction_counter_as_int () with
  | Ok value -> Proofview.tclUNIT value
  | Error message -> Tacticals.tclZEROMSG (Pp.str message)

let _ = define "complexity_class_names" (ret string) Api.complexity_class_names

let _ =
  define "string_of_complexity" (valexpr @-> ret string) @@ fun complexity ->
  Api.string_of_complexity (to_complexity complexity)

let _ =
  define "complexity_of_string" (string @-> ret (option valexpr)) @@ fun string ->
  Option.map of_complexity (Api.complexity_of_string string)

let _ =
  define "make_holdout_options"
    (bool @-> bool @-> int @-> float @-> float @-> ret valexpr)
    @@ fun holdout holdout_tail holdout_folds holdout_tail_fraction
           holdout_stability_threshold ->
  of_holdout_options
    (Api.make_holdout_options holdout holdout_tail holdout_folds
       (Float64.to_float holdout_tail_fraction)
       (Float64.to_float holdout_stability_threshold))

let _ = define "default_holdout_options" (ret valexpr) default_holdout_options
let _ = define "default_max_delta_bic" (ret float) (Float64.of_float 2.0)

let _ =
  define "run_fit" (valexpr @-> list valexpr @-> ret valexpr) @@ fun options samples ->
  let holdout_options, normalize_samples, fit_parameter_scale = to_fit_options options in
  let samples = List.map to_sample samples in
  Api.run_fit ~holdout_options ~normalize_samples fit_parameter_scale samples
  |> of_api_result (Tac2ffi.of_ext fit_result_tag)

let _ =
  define "run_assert" (valexpr @-> valexpr @-> list valexpr @-> ret valexpr)
    @@ fun options expected samples ->
  let holdout_options, normalize_samples, max_delta_bic = to_assert_options options in
  let expected = to_complexity expected in
  let samples = List.map to_sample samples in
  Api.run_assert ~holdout_options ~normalize_samples ~max_delta_bic ~expected samples
  |> of_api_result of_assert_result

let _ =
  define "fit_result_normalized" (fit_result @-> ret bool) @@ fun result ->
  result.Api.normalized

let _ =
  define "fit_result_normalization" (fit_result @-> ret (option valexpr)) @@ fun result ->
  Option.map of_sample_normalization result.Api.normalization

let _ =
  define "fit_result_samples" (fit_result @-> ret (list valexpr)) @@ fun result ->
  List.map of_sample result.Api.samples

let _ =
  define "fit_result_estimate" (fit_result @-> ret valexpr) @@ fun result ->
  of_estimate result.Api.estimate

let _ =
  define "fit_result_display_fits" (fit_result @-> ret (list valexpr)) @@ fun result ->
  List.map of_display_fit result.Api.display_fits

let _ =
  define "fit_result_parameter_scale_description" (fit_result @-> ret string) @@ fun result ->
  result.Api.fit_parameter_scale_description

let _ =
  define "fit_result_suspicious_relative_rmse" (fit_result @-> ret (option float))
    @@ fun result -> Option.map Float64.of_float result.Api.suspicious_relative_rmse

let _ =
  define "fit_result_holdout_stability_warning"
    (fit_result @-> ret (option (pair float float)))
    @@ fun result ->
  Option.map
    (fun (support, threshold) -> (Float64.of_float support, Float64.of_float threshold))
    result.Api.holdout_stability_warning

let _ =
  define "fit_result_holdout_summaries" (fit_result @-> ret (list valexpr))
    @@ fun result -> List.map of_holdout_summary result.Api.holdout_summaries
