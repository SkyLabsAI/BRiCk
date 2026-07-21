Require Import Ltac2.Ltac2.
Require Import skylabs.guesstimator.Guesstimator.
Require skylabs.guesstimator.Util.

Ltac2 fail (message : string) := Control.throw_invalid_argument message.

Ltac2 check_true (message : string) (value : bool) :=
  match value with
  | true => ()
  | false => fail message
  end.

Ltac2 check_string (message : string) (actual : string) (expected : string) :=
  check_true message (String.equal actual expected).

Ltac2 f (s : string) : float := float_of_string s.
Ltac2 fi (n : int) : float := float_of_int n.

Ltac2 mk_sample (problem_size_string : string) (time_string : string) : float sample :=
  { problem_size := f problem_size_string; time := f time_string }.

Ltac2 samples () : float sample list :=
  [ mk_sample "1" "1";
    mk_sample "2" "1";
    mk_sample "3" "1";
    mk_sample "4" "1";
    mk_sample "5" "1";
    mk_sample "6" "1";
    mk_sample "7" "1";
    mk_sample "8" "1" ].

Ltac2 options () : holdout_options :=
  make_holdout_options false false 5 (f "0.25") (f "0.80").

Ltac2 fit_run_options () : fit_options :=
  { fit_options_holdout := options ();
    fit_options_normalization := Unnormalized;
    fit_options_parameter_scale := FitParameterScaleOriginal }.

Ltac2 check_api_error_api () :=
  check_string "unexpected API error rendering"
    (api_error_to_string (ApiErrorString "example")) "example".

Ltac2 check_complexity_api () :=
  check_true "complexity class list should be nonempty"
    (Int.lt 0 (String.length complexity_class_names));
  check_string "unexpected polynomial rendering"
    (string_of_complexity (ComplexityPolynomial 2)) "polynomial-2";
  check_string "unexpected float rendering"
    (Message.to_string (pp_float () (f "1.25"))) "1.25";
  match complexity_of_string "polynomial-2" with
  | Some (ComplexityPolynomial degree) =>
      check_true "unexpected polynomial degree" (Int.equal degree 2)
  | _ => fail "failed to parse polynomial complexity"
  end.

Ltac2 check_default_holdout_options (options : holdout_options) :=
  check_true "holdout should be disabled by default"
    (Bool.neg (options.(holdout)));
  check_true "tail holdout should be disabled by default"
    (Bool.neg (options.(holdout_tail)));
  check_true "unexpected default holdout fold count"
    (Int.equal (options.(holdout_folds)) 5);
  check_true "unexpected default tail holdout fraction"
    (Float.equal (options.(holdout_tail_fraction)) (f "0.25"));
  check_true "unexpected default holdout stability threshold"
    (Float.equal (options.(holdout_stability_threshold)) (f "0.80")).

Ltac2 check_default_options () :=
  check_default_holdout_options (default_fit_options.(fit_options_holdout));
  match (default_fit_options.(fit_options_normalization)) with
  | Normalized => ()
  | _ => fail "fit should normalize samples by default"
  end;
  match (default_fit_options.(fit_options_parameter_scale)) with
  | FitParameterScaleOriginal => ()
  | _ => fail "fit should display parameters in the original scale by default"
  end;
  check_default_holdout_options (default_assert_options.(assert_options_holdout));
  match (default_assert_options.(assert_options_normalization)) with
  | Normalized => ()
  | _ => fail "assert should normalize samples by default"
  end;
  check_true "unexpected default maximum BIC delta"
    (Float.equal (default_assert_options.(assert_options_max_delta_bic)) (f "2.0")).

Ltac2 check_fit_api () :=
  match run_fit (fit_run_options ()) (samples ()) with
  | ApiError error => fail (api_error_to_string error)
  | ApiOk result =>
      check_true "fit result should not be normalized"
        (Bool.neg (fit_result_normalized result));
      match fit_result_normalization result with
      | None => ()
      | Some _ => fail "normalization should be absent"
      end;
      match fit_result_samples result with
      | [] => fail "fit result samples should be nonempty"
      | _ :: _ => ()
      end;
      let estimate := fit_result_estimate result in
      match estimate.(best).(model) with
      | ComplexityConstant => ()
      | _ => fail "constant samples should be classified as constant"
      end;
      match fit_result_display_fits result with
      | [] => fail "display fits should be nonempty"
      | _ :: _ => ()
      end;
      check_string "unexpected parameter scale description"
        (fit_result_parameter_scale_description result) "input problem size";
      match fit_result_suspicious_relative_rmse result with
      | None => ()
      | Some _ => fail "constant fit should not be suspicious"
      end;
      match fit_result_holdout_stability_warning result with
      | None => ()
      | Some _ => fail "holdout warning should be absent when holdout is disabled"
      end;
      match fit_result_holdout_summaries result with
      | [] => ()
      | _ :: _ => fail "holdout summaries should be empty when holdout is disabled"
      end
  end.

Ltac2 check_assert_api () :=
  match run_assert default_assert_options ComplexityConstant (samples ()) with
  | ApiError error => fail (api_error_to_string error)
  | ApiOk AssertOk => ()
  | ApiOk _ => fail "constant samples should satisfy a constant assertion"
  end.

Ltac2 check_util_api () :=
  match Util.instructions_result () with
  | ApiError _ => ()
  | ApiOk _ =>
      let (count, result) := Util.with_instructions (fun x => x) 7 in
      check_true "instruction count should be nonnegative" (Int.le 0 count);
      check_true "with_instructions should return the function result"
        (Int.equal result 7);
      let measured :=
        Util.sample
          (Util.Sampler.MinOf 3)
          1
          (fun _ => ())
          (fun _ => ())
          [(fi 1, ()); (fi 2, ()); (fi 3, ())]
      in
      match measured with
      | _ :: _ :: _ :: [] => ()
      | _ => fail "Util.sample should return one sample per input"
      end
  end.

Ltac2 Eval check_api_error_api ().
Ltac2 Eval check_complexity_api ().
Ltac2 Eval check_default_options ().
Ltac2 Eval check_fit_api ().
Ltac2 Eval check_assert_api ().
Ltac2 Eval check_util_api ().
