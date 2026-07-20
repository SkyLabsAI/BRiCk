Require Import Ltac2.Ltac2.
Require Import skylabs.guesstimator.Guesstimator.
Require skylabs.guesstimator.Util.

Ltac2 fail (message : string) := Control.throw_invalid_argument message.

Ltac2 check_true (message : string) (value : bool) :=
  match value with
  | true => ()
  | false => fail message
  end.

Ltac2 f (s : string) : float := float_of_string s.

Ltac2 Type search_case := {
  search_size : int;
  search_target : int;
  search_expected : bool;
  search_values : int list;
}.

Ltac2 rec descending_positive (n : int) : int list :=
  match Int.le n 0 with
  | true => []
  | false => n :: descending_positive (Int.sub n 1)
  end.

(** [unsorted_values n] contains [1..n], but is deliberately not monotone for
    [n > 1]: [n - 1; ...; 1; n]. *)
Ltac2 unsorted_values (n : int) : int list :=
  List.append (descending_positive (Int.sub n 1)) [n].

Ltac2 make_case
    (target_of_size : int -> int)
    (expected : bool)
    (n : int) : search_case :=
  { search_size := n;
    search_target := target_of_size n;
    search_expected := expected;
    search_values := unsorted_values n }.

(** Use many irregularly spaced points over a wide range so occasional
    instruction-count noise does not dominate the complexity fit. *)
Ltac2 sizes () : int list :=
  [95; 283; 401; 695; 753; 907; 1075; 1266; 1400; 1614;
   1666; 1850; 2058; 2269; 2331; 2506; 2768; 2928; 2955; 3153;
   3320; 3514; 3652; 3834; 3961; 4101; 4342; 4378; 4564; 4757;
   4872; 5007; 5312; 5359; 5589; 5681; 5870; 6065; 6239; 6290;
   6490; 6615; 6899; 7009; 7178; 7255; 7549; 7666; 7749; 7952;
   8122; 8335; 8385; 8577; 8796; 8840; 9135; 9280; 9367; 9597;
   9646; 9874; 10028; 10144; 10391; 10506; 10712; 10829; 11049; 11174;
   11342; 11488; 11651; 11713; 11966; 12053; 12177; 12469; 12617; 12734;
   12837; 13014; 13158; 13299; 13457; 13759; 13784; 13929; 14156; 14341;
   14474; 14670; 14759; 14909; 15103; 15179; 15271; 15352; 15403; 15456].

Ltac2 missing_cases () : search_case list :=
  List.map (make_case (fun _ => 0) false) (sizes ()).

Ltac2 last_cases () : search_case list :=
  List.map (make_case (fun n => n) true) (sizes ()).

Ltac2 almost_last_cases () : search_case list :=
  List.map (make_case (fun _ => 1) true) (sizes ()).

Ltac2 rec contains (target : int) (values : int list) : bool :=
  match values with
  | [] => false
  | value :: values =>
      match Int.equal target value with
      | true => true
      | false => contains target values
      end
  end.

Ltac2 find_opt_contains (target : int) (values : int list) : bool :=
  match List.find_opt (fun value => Int.equal target value) values with
  | Some _ => true
  | None => false
  end.

Ltac2 repetitions : int := 3.

Ltac2 run_contains (input : search_case) : unit :=
  check_true "unexpected result from recursive list search"
    (Bool.equal
       (contains (input.(search_target)) (input.(search_values)))
       (input.(search_expected))).

Ltac2 run_find_opt_contains (input : search_case) : unit :=
  check_true "unexpected result from List.find_opt search"
    (Bool.equal
       (find_opt_contains (input.(search_target)) (input.(search_values)))
       (input.(search_expected))).

Ltac2 problem_size_of_case (input : search_case) : problem_size :=
  float_of_int (input.(search_size)).

Require Import Ltac2.Printf.

Ltac2 assert_linear (run : search_case -> unit) (inputs : search_case list) : _ :=
  let inputs := List.map (fun input => (problem_size_of_case input, input)) inputs in
  let measured := Util.sample (Util.Sampler.MinOf repetitions) 1 (fun _ => ()) run inputs in
  let fail_with_data msg :=
    let msg :=
      List.fold_right
        (fun s acc =>
           (Message.concat acc
              (Message.concat (Message.force_new_line) (
                   fprintf "%a,%i" pp_float (s.(problem_size)) (s.(time))
                 )
              )
           )
        ) measured (Message.of_string msg) in
    let msg := Message.to_string msg in
    fail msg
  in
  let measured := List.map (map_sample float_of_int) measured in
  let options :=
    { assert_options_holdout :=
        make_holdout_options false false 5 (f "0.25") (f "0.80");
      assert_options_normalization := Normalized;
      assert_options_max_delta_bic := f "10" }
  in
  match run_assert options (ComplexityPolynomial 1) measured with
  | ApiOk AssertOk => ()
  | ApiOk AssertMismatch => fail_with_data "unsorted list search was not classified as linear"
  | ApiOk (AssertSuspicious _) => fail_with_data "unsorted list search fit was suspicious"
  | ApiOk (AssertUnstable _) => fail_with_data "unsorted list search fit was unstable"
  | ApiError error => fail_with_data (api_error_to_string error)
  | ApiOk _ => fail_with_data "unexpected assert result for unsorted list search"
  end.

Ltac2 when_instruction_counter_is_available (test : unit -> unit) : unit :=
  match Util.instructions_result () with
  | ApiError _ => ()
  | ApiOk _ => test ()
  end.

Ltac2 check_missing_recursive_search_is_linear () :=
  when_instruction_counter_is_available
    (fun () => assert_linear run_contains (missing_cases ())).

Ltac2 check_last_recursive_search_is_linear () :=
  when_instruction_counter_is_available
    (fun () => assert_linear run_contains (last_cases ())).

Ltac2 check_almost_last_find_opt_search_is_linear () :=
  when_instruction_counter_is_available
    (fun () => assert_linear run_find_opt_contains (almost_last_cases ())).

Ltac2 Eval check_missing_recursive_search_is_linear ().
Ltac2 Eval check_last_recursive_search_is_linear ().
Ltac2 Eval check_almost_last_find_opt_search_is_linear ().
