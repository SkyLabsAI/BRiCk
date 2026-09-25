open Guesstimator.Core

let fail message = failwith message
let require condition message = if not condition then fail message

let require_close ?(epsilon = 1e-12) label expected actual =
  if abs_float (expected -. actual) > epsilon then
    fail (Printf.sprintf "%s: expected %.12g, got %.12g" label expected actual)

let get = function Ok value -> value | Error message -> fail message

let require_error label = function
  | Ok _ -> fail (label ^ ": expected an error")
  | Error _ -> ()

let test_normalizes_problem_sizes_only () =
  let samples =
    [
      { problem_size = 2.0; time = 10.0 };
      { problem_size = 4.0; time = 20.0 };
      { problem_size = 8.0; time = 30.0 };
    ]
  in
  let normalization = get (sample_normalization samples) in
  require_close "scale" 8.0 normalization.problem_size_scale;
  let normalized = normalize_samples_with normalization samples in
  let expected_problem_sizes = [ 0.25; 0.5; 1.0 ] in
  let expected_times = [ 10.0; 20.0; 30.0 ] in
  List.iter2
    (fun sample expected_problem_size ->
      require_close "normalized problem size" expected_problem_size sample.problem_size)
    normalized expected_problem_sizes;
  List.iter2
    (fun sample expected_time -> require_close "unchanged time" expected_time sample.time)
    normalized expected_times

let test_repeated_sizes_remain_equal () =
  let samples =
    [
      { problem_size = 2.0; time = 1.0 };
      { problem_size = 2.0; time = 1.1 };
      { problem_size = 4.0; time = 2.0 };
    ]
  in
  let normalized = get (normalize_samples samples) in
  match normalized with
  | first :: second :: third :: [] ->
      require_close "first repeated size" first.problem_size second.problem_size;
      require_close "max size" 1.0 third.problem_size
  | _ -> fail "expected three normalized samples"

let test_rejects_invalid_problem_sizes () =
  require_error "empty" (sample_normalization []);
  require_error "zero"
    (normalize_samples
       [
         { problem_size = 0.0; time = 1.0 };
         { problem_size = 1.0; time = 2.0 };
       ]);
  require_error "negative"
    (normalize_samples [ { problem_size = -1.0; time = 1.0 } ]);
  require_error "infinite"
    (normalize_samples [ { problem_size = infinity; time = 1.0 } ])

let () =
  test_normalizes_problem_sizes_only ();
  test_repeated_sizes_remain_equal ();
  test_rejects_invalid_problem_sizes ()
