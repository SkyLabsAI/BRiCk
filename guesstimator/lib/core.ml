type complexity =
  | Constant
  | Logarithmic
  | Polynomial of int
  | QuasiPolynomial of int
  | PowerLaw
  | Exponential

type constant
type logarithmic
type polynomial
type quasi_polynomial
type powerlaw
type exponential

module Model = struct
  type _ t =
  | Constant : constant t
  | Logarithmic : logarithmic t
  | Polynomial : float array -> polynomial t
  | QuasiPolynomial : float array -> quasi_polynomial t
  | PowerLaw : powerlaw t
  | Exponential : exponential t

  type any = Model : 'm t -> any
end

type sample = {
  problem_size : float;
  time : float;
}

type sample_normalization = {
  problem_size_scale : float;
}

type parameter = string * float

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
  within_comparisons : comparison list;
}

let fixed_models = [ Constant; Logarithmic; PowerLaw; Exponential ]
let epsilon = 1e-12
let model_selection_noise_floor_relative = 4.0 *. epsilon_float
let close_model_bic_delta = 2.0
let nan = 0.0 /. 0.0

let ( let* ) r f = match r with Ok x -> f x | Error _ as e -> e

let polynomial degree = Polynomial degree
let quasi_polynomial degree = QuasiPolynomial degree

let polynomial_degree = function
  | Polynomial degree when degree >= 1 -> Some degree
  | Constant | Logarithmic | Polynomial _ | QuasiPolynomial _ | PowerLaw | Exponential -> None

let quasi_polynomial_degree = function
  | QuasiPolynomial degree when degree >= 1 -> Some degree
  | Constant | Logarithmic | Polynomial _ | QuasiPolynomial _ | PowerLaw | Exponential -> None

let string_of_complexity = function
  | Constant -> "constant"
  | Logarithmic -> "logarithmic"
  | Polynomial degree -> Printf.sprintf "polynomial-%d" degree
  | QuasiPolynomial degree -> Printf.sprintf "quasi-polynomial-%d" degree
  | PowerLaw -> "power-law"
  | Exponential -> "exponential"

let string_has_prefix ~prefix string =
  let prefix_length = String.length prefix in
  String.length string >= prefix_length
  && String.sub string 0 prefix_length = prefix

let complexity_of_string string =
  let parse_degree ~prefix constructor =
    if string_has_prefix ~prefix string then
      let prefix_length = String.length prefix in
      let degree_string =
        String.sub string prefix_length (String.length string - prefix_length)
      in
      match int_of_string_opt degree_string with
      | Some degree when degree >= 1 -> Some (constructor degree)
      | Some _ | None -> None
    else None
  in
  match string with
  | "constant" -> Some Constant
  | "logarithmic" -> Some Logarithmic
  | "power-law" -> Some PowerLaw
  | "exponential" -> Some Exponential
  | _ -> (
      match parse_degree ~prefix:"polynomial-" polynomial with
      | Some _ as parsed -> parsed
      | None -> parse_degree ~prefix:"quasi-polynomial-" quasi_polynomial )

type complexity_class =
  | Constant_class
  | Logarithmic_class
  | Polynomial_class
  | QuasiPolynomial_class
  | PowerLaw_class
  | Exponential_class

let complexity_class = function
  | Constant -> Constant_class
  | Logarithmic -> Logarithmic_class
  | Polynomial _ -> Polynomial_class
  | QuasiPolynomial _ -> QuasiPolynomial_class
  | PowerLaw -> PowerLaw_class
  | Exponential -> Exponential_class

let same_complexity_class left right = complexity_class left = complexity_class right

let parameter_count = function
  | Constant -> 1
  | Logarithmic | PowerLaw | Exponential -> 2
  | Polynomial degree | QuasiPolynomial degree -> degree + 1

let is_finite x =
  match classify_float x with FP_nan | FP_infinite -> false | _ -> true

let safe_exp x =
  if not (is_finite x) then nan
  else if x > log max_float then infinity
  else if x < log min_float then 0.0
  else exp x

let sample_normalization samples =
  match samples with
  | [] -> Error "cannot normalize empty sample set"
  | first :: rest ->
      if (not (is_finite first.problem_size)) || first.problem_size <= 0.0 then
        Error "normalization requires finite positive problem sizes"
      else
        let rec loop maximum = function
          | [] -> Ok { problem_size_scale = maximum }
          | sample :: samples ->
              if (not (is_finite sample.problem_size)) || sample.problem_size <= 0.0 then
                Error "normalization requires finite positive problem sizes"
              else loop (max maximum sample.problem_size) samples
        in
        loop first.problem_size rest

let normalize_samples_with normalization samples =
  let scale = normalization.problem_size_scale in
  if (not (is_finite scale)) || scale <= 0.0 then
    invalid_arg "normalize_samples_with requires a finite positive problem_size_scale"
  else
    List.map
      (fun sample -> { sample with problem_size = sample.problem_size /. scale })
      samples

let normalize_samples samples =
  let* normalization = sample_normalization samples in
  Ok (normalize_samples_with normalization samples)

let validate_samples samples =
  let count = List.length samples in
  if count < 3 then Error "need at least three observations"
  else
    match
      List.find_opt
        (fun s ->
          (not (is_finite s.problem_size))
          || (not (is_finite s.time))
          || s.problem_size <= 0.0 || s.time <= 0.0)
        samples
    with
    | Some _ -> Error "all problem sizes and times must be finite positive numbers"
    | None -> Ok ()

let validate_model = function
  | Polynomial degree when degree < 1 -> Error "polynomial degree must be at least 1"
  | QuasiPolynomial degree when degree < 1 -> Error "quasi-polynomial degree must be at least 1"
  | Constant | Logarithmic | Polynomial _ | QuasiPolynomial _ | PowerLaw | Exponential -> Ok ()

let validate_model_samples model samples =
  let* () = validate_model model in
  let* () = validate_samples samples in
  let observations = List.length samples in
  let parameters = parameter_count model in
  if observations <= parameters then
    Error
      (Printf.sprintf "need more observations than model parameters (%d)" parameters)
  else Ok ()

let stable_sum_squares values =
  let scale = ref 0.0 in
  let sumsq = ref 1.0 in
  List.iter
    (fun value ->
      let value = abs_float value in
      if value <> 0.0 then
        if value > !scale then (
          let ratio = if !scale = 0.0 then 0.0 else !scale /. value in
          sumsq := 1.0 +. (!sumsq *. ratio *. ratio);
          scale := value)
        else
          let ratio = value /. !scale in
          sumsq := !sumsq +. (ratio *. ratio))
    values;
  if !scale = 0.0 then 0.0
  else
    let scale_limit = sqrt (max_float /. !sumsq) in
    if !scale > scale_limit then max_float else (!scale *. !scale) *. !sumsq

let residual_roundoff_tolerance_from_scale scale =
  if is_finite scale && scale > 0.0 then epsilon *. epsilon *. scale else 0.0

let residual_noise_floor_from_scale scale =
  if is_finite scale && scale > 0.0 then
    model_selection_noise_floor_relative *. scale
  else 0.0

let sample_mean samples =
  let count = ref 0 in
  let mean = ref 0.0 in
  List.iter
    (fun sample ->
      incr count;
      mean := !mean +. ((sample.time -. !mean) /. float_of_int !count))
    samples;
  !mean

let residual_variation_scale samples =
  match samples with
  | [] -> 0.0
  | _ ->
      let mean_time = sample_mean samples in
      let tss = stable_sum_squares (List.map (fun sample -> sample.time -. mean_time) samples) in
      if tss > 0.0 then tss
      else stable_sum_squares (List.map (fun sample -> sample.time) samples)

let residual_roundoff_tolerance samples =
  residual_roundoff_tolerance_from_scale (residual_variation_scale samples)

let residual_noise_floor samples =
  residual_noise_floor_from_scale (residual_variation_scale samples)

exception Singular
exception Regression_error of string

let regression_error message = raise (Regression_error message)

let require_finite message value =
  if not (is_finite value) then regression_error message

let stable_norm vector =
  let scale = ref 0.0 in
  let sumsq = ref 1.0 in
  Array.iter
    (fun value ->
      let value = abs_float value in
      if value <> 0.0 then
        if value > !scale then (
          let ratio = if !scale = 0.0 then 0.0 else !scale /. value in
          sumsq := 1.0 +. (!sumsq *. ratio *. ratio);
          scale := value)
        else
          let ratio = value /. !scale in
          sumsq := !sumsq +. (ratio *. ratio))
    vector;
  if !scale = 0.0 then 0.0 else !scale *. sqrt !sumsq

let dot a b =
  let total = ref 0.0 in
  for i = 0 to Array.length a - 1 do
    total := !total +. (a.(i) *. b.(i))
  done;
  !total

let linear_regression rows ys =
  let n = Array.length ys in
  if n = 0 then Error "empty regression"
  else
    let p = Array.length rows.(0) in
    if p = 0 then Error "empty regression design"
    else if Array.exists (fun row -> Array.length row <> p) rows then
      Error "regression design has inconsistent row lengths"
    else
      try
        Array.iter (require_finite "regression response contains non-finite values") ys;
        let column_scales = Array.make p 0.0 in
        for i = 0 to n - 1 do
          let row = rows.(i) in
          for j = 0 to p - 1 do
            let value = row.(j) in
            require_finite "regression design contains non-finite values" value;
            column_scales.(j) <- max column_scales.(j) (abs_float value)
          done
        done;
        for j = 0 to p - 1 do
          if column_scales.(j) = 0.0 then raise Singular
        done;
        let scaled_columns =
          Array.init p (fun j ->
              Array.init n (fun i -> rows.(i).(j) /. column_scales.(j)))
        in
        let q = Array.init p (fun _ -> Array.make n 0.0) in
        let r = Array.init p (fun _ -> Array.make p 0.0) in
        let rank_tolerance = 1e-10 *. sqrt (float_of_int n) in
        for j = 0 to p - 1 do
          let v = Array.copy scaled_columns.(j) in
          for pass = 1 to 2 do
            ignore pass;
            for i = 0 to j - 1 do
              let rij = dot q.(i) v in
              r.(i).(j) <- r.(i).(j) +. rij;
              for k = 0 to n - 1 do
                v.(k) <- v.(k) -. (rij *. q.(i).(k))
              done
            done
          done;
          let norm = stable_norm v in
          require_finite "regression produced non-finite values" norm;
          if norm <= rank_tolerance then raise Singular;
          r.(j).(j) <- norm;
          for k = 0 to n - 1 do
            q.(j).(k) <- v.(k) /. norm
          done
        done;
        let qty =
          Array.init p (fun j ->
              let value = dot q.(j) ys in
              require_finite "regression produced non-finite values" value;
              value)
        in
        let scaled_solution = Array.make p 0.0 in
        for i = p - 1 downto 0 do
          let total = ref qty.(i) in
          for j = i + 1 to p - 1 do
            total := !total -. (r.(i).(j) *. scaled_solution.(j))
          done;
          if abs_float r.(i).(i) <= rank_tolerance then raise Singular;
          scaled_solution.(i) <- !total /. r.(i).(i);
          require_finite "regression produced non-finite coefficients" scaled_solution.(i)
        done;
        let solution =
          Array.mapi
            (fun j coefficient ->
              let value = coefficient /. column_scales.(j) in
              require_finite "regression produced non-finite coefficients" value;
              value)
            scaled_solution
        in
        Ok solution
      with
      | Singular -> Error "rank deficient regression matrix; data do not identify this model"
      | Regression_error message -> Error message

let polynomial_row degree problem_size =
  let row = Array.make (degree + 1) 1.0 in
  for i = 1 to degree do
    row.(i) <- row.(i - 1) *. problem_size
  done;
  row

let quasi_polynomial_row degree problem_size =
  let row = polynomial_row degree problem_size in
  row.(degree) <- row.(degree) *. log problem_size;
  row

let binomial n k =
  if k < 0 || k > n then 0.0
  else
    let k = min k (n - k) in
    let coefficient = ref 1.0 in
    for i = 1 to k do
      coefficient :=
        !coefficient *. float_of_int (n - k + i) /. float_of_int i
    done;
    !coefficient

let polynomial_center_and_scale samples =
  match samples with
  | [] -> (0.0, 1.0)
  | first :: rest ->
      let lo, hi =
        List.fold_left
          (fun (lo, hi) sample ->
            (min lo sample.problem_size, max hi sample.problem_size))
          (first.problem_size, first.problem_size) rest
      in
      let span = hi -. lo in
      let center = lo +. (span /. 2.0) in
      let scale = max (abs_float (hi -. center)) (abs_float (center -. lo)) in
      let scale = if scale > 0.0 && is_finite scale then scale else 1.0 in
      (center, scale)

let transform_scaled_polynomial_coefficients ~center ~scale coefficients =
  let degree = Array.length coefficients - 1 in
  let transformed = Array.make (degree + 1) 0.0 in
  let center_over_scale = -.center /. scale in
  for j = 0 to degree do
    for i = 0 to j do
      let term =
        coefficients.(j) *. binomial j i
        *. (center_over_scale ** float_of_int (j - i))
        /. (scale ** float_of_int i)
      in
      transformed.(i) <- transformed.(i) +. term
    done
  done;
  if Array.for_all is_finite transformed then Ok transformed
  else Error "regression produced non-finite coefficients"

let polynomial_regression degree samples =
  let center, scale = polynomial_center_and_scale samples in
  let row_and_y sample =
    let z = (sample.problem_size -. center) /. scale in
    (polynomial_row degree z, sample.time)
  in
  let pairs = List.map row_and_y samples in
  let rows = Array.of_list (List.map fst pairs) in
  let ys = Array.of_list (List.map snd pairs) in
  let* scaled_coefficients = linear_regression rows ys in
  transform_scaled_polynomial_coefficients ~center ~scale scaled_coefficients

let feature_center_and_scale values =
  match values with
  | [] -> (0.0, 1.0)
  | first :: rest ->
      let lo, hi =
        List.fold_left (fun (lo, hi) value -> (min lo value, max hi value)) (first, first)
          rest
      in
      let span = hi -. lo in
      let center = lo +. (span /. 2.0) in
      let scale = max (abs_float (hi -. center)) (abs_float (center -. lo)) in
      let scale = if scale > 0.0 && is_finite scale then scale else 1.0 in
      (center, scale)

let two_parameter_feature_regression ~feature ~response samples =
  let features = List.map feature samples in
  let center, scale = feature_center_and_scale features in
  let rows =
    features
    |> List.map (fun value -> [| 1.0; (value -. center) /. scale |])
    |> Array.of_list
  in
  let ys = samples |> List.map response |> Array.of_list in
  let* scaled_coefficients = linear_regression rows ys in
  let slope = scaled_coefficients.(1) /. scale in
  let intercept = scaled_coefficients.(0) -. (slope *. center) in
  if is_finite intercept && is_finite slope then Ok [| intercept; slope |]
  else Error "regression produced non-finite coefficients"

let transformed_regression model samples =
  match model with
  | Logarithmic ->
      two_parameter_feature_regression ~feature:(fun s -> log s.problem_size)
        ~response:(fun s -> s.time) samples
  | PowerLaw ->
      two_parameter_feature_regression ~feature:(fun s -> log s.problem_size)
        ~response:(fun s -> log s.time) samples
  | Exponential ->
      two_parameter_feature_regression ~feature:(fun s -> s.problem_size)
        ~response:(fun s -> log s.time) samples
  | Constant | Polynomial _ | QuasiPolynomial _ ->
      let row_and_y s =
        match model with
        | Constant -> ([| 1.0 |], s.time)
        | Polynomial degree -> (polynomial_row degree s.problem_size, s.time)
        | QuasiPolynomial degree -> (quasi_polynomial_row degree s.problem_size, s.time)
        | Logarithmic | PowerLaw | Exponential -> invalid_arg "transformed_regression"
      in
      let pairs = List.map row_and_y samples in
      let rows = Array.of_list (List.map fst pairs) in
      let ys = Array.of_list (List.map snd pairs) in
      linear_regression rows ys

let min_max values =
  match values with
  | [] -> Error "empty regression"
  | x :: xs ->
      Ok
        (List.fold_left
           (fun (lo, hi) x -> (min lo x, max hi x))
           (x, x) xs)

let scale_for_slope ~feature samples slope =
  let etas = List.map (fun s -> slope *. feature s) samples in
  if List.exists (fun x -> not (is_finite x)) etas then None
  else
    let max_eta = List.fold_left max neg_infinity etas in
    let weights = List.map (fun eta -> exp (eta -. max_eta)) etas in
    let numerator, denominator =
      List.fold_left2
        (fun (numerator, denominator) s weight ->
          (numerator +. (s.time *. weight), denominator +. (weight *. weight)))
        (0.0, 0.0) samples weights
    in
    if denominator <= epsilon then None
    else
      let scaled_coefficient = numerator /. denominator in
      if scaled_coefficient <= 0.0 || not (is_finite scaled_coefficient) then None
      else
        let rss =
          List.fold_left2
            (fun total s weight ->
              let residual = s.time -. (scaled_coefficient *. weight) in
              total +. (residual *. residual))
            0.0 samples weights
        in
        let log_coefficient = log scaled_coefficient -. max_eta in
        if is_finite rss && is_finite log_coefficient then Some (rss, log_coefficient) else None

let objective_for_slope ~feature samples slope =
  match scale_for_slope ~feature samples slope with Some (rss, _) -> rss | None -> infinity

let bracket_minimum objective initial_slope step =
  let f0 = objective initial_slope in
  let left = initial_slope -. step in
  let right = initial_slope +. step in
  let f_left = objective left in
  let f_right = objective right in
  if f0 <= f_left && f0 <= f_right then (left, right)
  else
    let direction = if f_left < f_right then -1.0 else 1.0 in
    let rec expand previous current step remaining =
      if remaining = 0 then (min previous current, max previous current)
      else
        let next_step = step *. 2.0 in
        let next = current +. (direction *. next_step) in
        if not (is_finite next) then (min previous current, max previous current)
        else
          let f_current = objective current in
          let f_next = objective next in
          if (not (is_finite f_next)) || f_next >= f_current then
            (min previous next, max previous next)
          else expand current next next_step (remaining - 1)
    in
    let current = initial_slope +. (direction *. step) in
    expand initial_slope current step 60

let golden_section_search objective lo hi =
  let gr = (sqrt 5.0 -. 1.0) /. 2.0 in
  let rec loop a b c d fc fd remaining =
    if remaining = 0 || abs_float (b -. a) <= (1e-10 *. (1.0 +. abs_float ((a +. b) /. 2.0))) then
      if fc <= fd then c else d
    else if fc > fd then
      let a = c in
      let c = d in
      let fc = fd in
      let d = a +. (gr *. (b -. a)) in
      let fd = objective d in
      loop a b c d fc fd (remaining - 1)
    else
      let b = d in
      let d = c in
      let fd = fc in
      let c = b -. (gr *. (b -. a)) in
      let fc = objective c in
      loop a b c d fc fd (remaining - 1)
  in
  let c = hi -. (gr *. (hi -. lo)) in
  let d = lo +. (gr *. (hi -. lo)) in
  loop lo hi c d (objective c) (objective d) 120

let grid_minimum_interval objective lo hi intervals =
  let step = (hi -. lo) /. float_of_int intervals in
  let best_index = ref 0 in
  let best_value = ref (objective lo) in
  for index = 1 to intervals do
    let slope = lo +. (float_of_int index *. step) in
    let value = objective slope in
    if value < !best_value then (
      best_index := index;
      best_value := value)
  done;
  let slope index = lo +. (float_of_int index *. step) in
  let left_index = max 0 (!best_index - 1) in
  let right_index = min intervals (!best_index + 1) in
  (slope !best_index, slope left_index, slope right_index)

let best_slope ~feature samples initial_slope =
  let* lo, hi = min_max (List.map feature samples) in
  let span = hi -. lo in
  let range_step = if span > epsilon then 1.0 /. span else 1.0 in
  let step = max range_step (0.25 *. max 1.0 (abs_float initial_slope)) in
  let objective = objective_for_slope ~feature samples in
  let raw_radius = max (50.0 *. range_step) ((4.0 *. abs_float initial_slope) +. range_step) in
  let radius = if is_finite raw_radius then raw_radius else 50.0 *. range_step in
  let search_lo = initial_slope -. radius in
  let search_hi = initial_slope +. radius in
  let grid_slope, grid_lo, grid_hi = grid_minimum_interval objective search_lo search_hi 400 in
  let grid_optimized = golden_section_search objective grid_lo grid_hi in
  let bracket_lo, bracket_hi = bracket_minimum objective initial_slope step in
  let bracket_optimized = golden_section_search objective bracket_lo bracket_hi in
  let candidates =
    [
      initial_slope;
      grid_slope;
      grid_optimized;
      grid_lo;
      grid_hi;
      bracket_optimized;
      bracket_lo;
      bracket_hi;
    ]
  in
  let best =
    List.fold_left
      (fun best candidate -> if objective candidate < objective best then candidate else best)
      initial_slope candidates
  in
  Ok best

let nonlinear_regression model samples =
  let feature =
    match model with
    | PowerLaw -> fun s -> log s.problem_size
    | Exponential -> fun s -> s.problem_size
    | Constant | Logarithmic | Polynomial _ | QuasiPolynomial _ -> invalid_arg "nonlinear_regression"
  in
  let* initial = transformed_regression model samples in
  let initial_slope = if is_finite initial.(1) then initial.(1) else 0.0 in
  let* slope = best_slope ~feature samples initial_slope in
  match scale_for_slope ~feature samples slope with
  | Some (_, log_coefficient) -> Ok [| log_coefficient; slope |]
  | None -> Error "nonlinear regression failed to find finite parameters"

let regression_coefficients model samples =
  match model with
  | Polynomial degree -> polynomial_regression degree samples
  | PowerLaw | Exponential -> nonlinear_regression model samples
  | Constant | Logarithmic | QuasiPolynomial _ -> transformed_regression model samples

let polynomial_coefficient_name = function
  | 0 -> "intercept"
  | 1 -> "linear"
  | 2 -> "quadratic"
  | degree -> Printf.sprintf "degree_%d" degree

let quasi_polynomial_coefficient_name degree i =
  if i = degree then polynomial_coefficient_name i ^ "_log"
  else polynomial_coefficient_name i

let eval_polynomial_coefficients degree coefficients ~problem_size =
  let total = ref coefficients.(degree) in
  for i = degree - 1 downto 0 do
    total := (!total *. problem_size) +. coefficients.(i)
  done;
  !total

let eval_quasi_polynomial_coefficients degree coefficients ~problem_size =
  let lower_terms =
    if degree <= 0 then 0.0
    else eval_polynomial_coefficients (degree - 1) coefficients ~problem_size
  in
  let leading_coefficient = coefficients.(degree) in
  let leading_term =
    if leading_coefficient = 0.0 then 0.0
    else leading_coefficient *. (problem_size ** float_of_int degree) *. log problem_size
  in
  lower_terms +. leading_term

let parameters_of_named_coefficients coefficient_name degree coefficients =
  let rec loop i acc =
    if i < 0 then acc else loop (i - 1) ((coefficient_name i, coefficients.(i)) :: acc)
  in
  loop degree []

let parameters_of_polynomial_coefficients degree coefficients =
  parameters_of_named_coefficients polynomial_coefficient_name degree coefficients

let parameters_of_quasi_polynomial_coefficients degree coefficients =
  parameters_of_named_coefficients (quasi_polynomial_coefficient_name degree) degree coefficients

let model_with_coefficients model coefficients =
  match model with
  | Constant -> Model.Model Model.Constant
  | Logarithmic -> Model.Model Model.Logarithmic
  | Polynomial _ -> Model.Model (Model.Polynomial coefficients)
  | QuasiPolynomial _ -> Model.Model (Model.QuasiPolynomial coefficients)
  | PowerLaw -> Model.Model Model.PowerLaw
  | Exponential -> Model.Model Model.Exponential

let predict_from_model : type m. m Model.t -> float array -> problem_size:float -> float =
 fun model coefficients ~problem_size ->
  match model with
  | Model.Constant -> coefficients.(0)
  | Model.Logarithmic -> coefficients.(0) +. (coefficients.(1) *. log problem_size)
  | Model.Polynomial coefficients ->
      eval_polynomial_coefficients (Array.length coefficients - 1) coefficients ~problem_size
  | Model.QuasiPolynomial coefficients ->
      eval_quasi_polynomial_coefficients (Array.length coefficients - 1) coefficients ~problem_size
  | Model.PowerLaw -> exp (coefficients.(0) +. (coefficients.(1) *. log problem_size))
  | Model.Exponential -> exp (coefficients.(0) +. (coefficients.(1) *. problem_size))

let predict_from_coefficients model coefficients ~problem_size =
  let (Model.Model model) = model_with_coefficients model coefficients in
  predict_from_model model coefficients ~problem_size

let parameters_of_model : type m. m Model.t -> float array -> parameter list =
 fun model coefficients ->
  match model with
  | Model.Constant -> [ ("constant", coefficients.(0)) ]
  | Model.Logarithmic ->
      [ ("intercept", coefficients.(0)); ("log_coefficient", coefficients.(1)) ]
  | Model.Polynomial coefficients ->
      parameters_of_polynomial_coefficients (Array.length coefficients - 1) coefficients
  | Model.QuasiPolynomial coefficients ->
      parameters_of_quasi_polynomial_coefficients (Array.length coefficients - 1) coefficients
  | Model.PowerLaw ->
      [
        ("coefficient", safe_exp coefficients.(0));
        ("log_coefficient", coefficients.(0));
        ("exponent", coefficients.(1));
      ]
  | Model.Exponential ->
      [
        ("coefficient", safe_exp coefficients.(0));
        ("log_coefficient", coefficients.(0));
        ("rate", coefficients.(1));
      ]

let parameters_of_coefficients model coefficients =
  let (Model.Model model) = model_with_coefficients model coefficients in
  parameters_of_model model coefficients

let find_parameter name parameters =
  match List.assoc_opt name parameters with Some value -> value | None -> nan

let scale_power scale degree = scale ** float_of_int degree

let parameters_in_original_problem_size_scale normalization fitted =
  let scale = normalization.problem_size_scale in
  let log_scale = log scale in
  let parameter name = find_parameter name fitted.parameters in
  match fitted.model with
  | Constant -> fitted.parameters
  | Logarithmic ->
      let log_coefficient = parameter "log_coefficient" in
      [
        ("intercept", parameter "intercept" -. (log_coefficient *. log_scale));
        ("log_coefficient", log_coefficient);
      ]
  | Polynomial degree ->
      let coefficients =
        Array.init (degree + 1) (fun i ->
            parameter (polynomial_coefficient_name i) /. scale_power scale i)
      in
      parameters_of_polynomial_coefficients degree coefficients
  | QuasiPolynomial degree ->
      let coefficients = Array.make (degree + 1) 0.0 in
      for i = 0 to degree - 1 do
        coefficients.(i) <-
          parameter (quasi_polynomial_coefficient_name degree i) /. scale_power scale i
      done;
      let log_coefficient_name = quasi_polynomial_coefficient_name degree degree in
      let log_coefficient = parameter log_coefficient_name in
      let leading_scale = scale_power scale degree in
      coefficients.(degree) <- -.log_coefficient *. log_scale /. leading_scale;
      parameters_of_polynomial_coefficients degree coefficients
      @ [ (log_coefficient_name, log_coefficient /. leading_scale) ]
  | PowerLaw ->
      let exponent = parameter "exponent" in
      let log_coefficient = parameter "log_coefficient" -. (exponent *. log_scale) in
      [
        ("coefficient", safe_exp log_coefficient);
        ("log_coefficient", log_coefficient);
        ("exponent", exponent);
      ]
  | Exponential ->
      let log_coefficient = parameter "log_coefficient" in
      let rate = parameter "rate" /. scale in
      [
        ("coefficient", safe_exp log_coefficient);
        ("log_coefficient", log_coefficient);
        ("rate", rate);
      ]

let coefficients_from_parameters coefficient_name degree parameters =
  Array.init (degree + 1) (fun i -> find_parameter (coefficient_name i) parameters)

let predict fitted ~problem_size =
  match fitted.model with
  | Constant -> find_parameter "constant" fitted.parameters
  | Logarithmic ->
      find_parameter "intercept" fitted.parameters
      +. (find_parameter "log_coefficient" fitted.parameters *. log problem_size)
  | Polynomial degree ->
      let coefficients =
        coefficients_from_parameters polynomial_coefficient_name degree fitted.parameters
      in
      predict_from_model (Model.Polynomial coefficients) coefficients ~problem_size
  | QuasiPolynomial degree ->
      let coefficients =
        coefficients_from_parameters
          (quasi_polynomial_coefficient_name degree)
          degree fitted.parameters
      in
      predict_from_model (Model.QuasiPolynomial coefficients) coefficients ~problem_size
  | PowerLaw ->
      let exponent = find_parameter "exponent" fitted.parameters in
      let log_coefficient = find_parameter "log_coefficient" fitted.parameters in
      if is_finite log_coefficient then exp (log_coefficient +. (exponent *. log problem_size))
      else
        find_parameter "coefficient" fitted.parameters *. (problem_size ** exponent)
  | Exponential ->
      let rate = find_parameter "rate" fitted.parameters in
      let log_coefficient = find_parameter "log_coefficient" fitted.parameters in
      if is_finite log_coefficient then exp (log_coefficient +. (rate *. problem_size))
      else find_parameter "coefficient" fitted.parameters *. exp (rate *. problem_size)

let fit model samples =
  let* () = validate_model_samples model samples in
  let* coefficients = regression_coefficients model samples in
  let n = List.length samples in
  let k = parameter_count model in
  let residuals =
    List.map
      (fun s ->
        let prediction = predict_from_coefficients model coefficients ~problem_size:s.problem_size in
        s.time -. prediction)
      samples
  in
  if List.exists (fun residual -> not (is_finite residual)) residuals then
    Error "fit produced non-finite residual error"
  else
    let rss = stable_sum_squares residuals in
    let mean_time = sample_mean samples in
    let tss = stable_sum_squares (List.map (fun s -> s.time -. mean_time) samples) in
    let time_scale = stable_sum_squares (List.map (fun s -> s.time) samples) in
    if (not (is_finite tss)) || not (is_finite time_scale) then
      Error "fit produced non-finite summary statistics"
    else
      let r_squared_tolerance = epsilon *. time_scale in
      let r_squared =
        if tss <= r_squared_tolerance then
          if rss <= r_squared_tolerance then 1.0 else nan
        else 1.0 -. (rss /. tss)
      in
      (* For model selection, residuals below a small response-scale noise floor
         are not meaningful evidence for a more complex model. This keeps BIC
         from choosing high-degree polynomial or quasi-polynomial fits merely
         because they shave tiny residuals off an already near-perfect simpler
         fit. For non-constant responses, use the variation scale so a large
         offset does not hide real residual differences. For exact constants,
         [tss] is zero; use the observation scale so equivalent zero-residual
         fits are compared by parameter count. *)
      let residual_floor_scale = if tss > 0.0 then tss else time_scale in
      let residual_floor = residual_noise_floor_from_scale residual_floor_scale in
      let raw_variance = rss /. float_of_int n in
      let floor_variance = residual_floor /. float_of_int n in
      let variance =
        if floor_variance > 0.0 then max raw_variance floor_variance
        else if raw_variance <= 0.0 then min_float
        else raw_variance
      in
      let aic = (float_of_int n *. log variance) +. (2.0 *. float_of_int k) in
      let bic = (float_of_int n *. log variance) +. (float_of_int k *. log (float_of_int n)) in
      if
        (not (is_finite r_squared))
        || (not (is_finite aic)) || not (is_finite bic)
      then Error "fit produced non-finite summary statistics"
      else
        Ok
          {
            model;
            parameters = parameters_of_coefficients model coefficients;
            rss;
            r_squared;
            aic;
            bic;
            degrees_of_freedom = n - k;
            observations = n;
          }

(* Lanczos approximation and regularized beta are used only to compute the
   upper-tail probability of the F statistic without external dependencies. *)
let rec log_gamma z =
  let coefficients =
    [|
      0.99999999999980993;
      676.5203681218851;
      -1259.1392167224028;
      771.32342877765313;
      -176.61502916214059;
      12.507343278686905;
      -0.13857109526572012;
      9.9843695780195716e-6;
      1.5056327351493116e-7;
    |]
  in
  if z < 0.5 then log Float.pi -. log (sin (Float.pi *. z)) -. log_gamma (1.0 -. z)
  else
    let z = z -. 1.0 in
    let x = ref coefficients.(0) in
    for i = 1 to Array.length coefficients - 1 do
      x := !x +. (coefficients.(i) /. (z +. float_of_int i))
    done;
    let t = z +. 7.5 in
    (0.5 *. log (2.0 *. Float.pi)) +. ((z +. 0.5) *. log t) -. t +. log !x

let beta_continued_fraction a b x =
  let max_iterations = 200 in
  let eps = 3e-14 in
  let fpmin = 1e-300 in
  let qab = a +. b in
  let qap = a +. 1.0 in
  let qam = a -. 1.0 in
  let c = ref 1.0 in
  let d = ref (1.0 -. (qab *. x /. qap)) in
  if abs_float !d < fpmin then d := fpmin;
  d := 1.0 /. !d;
  let h = ref !d in
  let m = ref 1 in
  let stop = ref false in
  while (not !stop) && !m <= max_iterations do
    let m_float = float_of_int !m in
    let m2 = 2.0 *. m_float in
    let aa = m_float *. (b -. m_float) *. x /. ((qam +. m2) *. (a +. m2)) in
    d := 1.0 +. (aa *. !d);
    if abs_float !d < fpmin then d := fpmin;
    c := 1.0 +. (aa /. !c);
    if abs_float !c < fpmin then c := fpmin;
    d := 1.0 /. !d;
    h := !h *. !d *. !c;
    let aa = -.((a +. m_float) *. (qab +. m_float) *. x) /. ((a +. m2) *. (qap +. m2)) in
    d := 1.0 +. (aa *. !d);
    if abs_float !d < fpmin then d := fpmin;
    c := 1.0 +. (aa /. !c);
    if abs_float !c < fpmin then c := fpmin;
    d := 1.0 /. !d;
    let delta = !d *. !c in
    h := !h *. delta;
    if abs_float (delta -. 1.0) < eps then stop := true;
    incr m
  done;
  !h

let regularized_beta x a b =
  if x <= 0.0 then 0.0
  else if x >= 1.0 then 1.0
  else
    let bt =
      exp
        (log_gamma (a +. b) -. log_gamma a -. log_gamma b +. (a *. log x)
       +. (b *. log (1.0 -. x)))
    in
    if x < (a +. 1.0) /. (a +. b +. 2.0) then bt *. beta_continued_fraction a b x /. a
    else 1.0 -. (bt *. beta_continued_fraction b a (1.0 -. x) /. b)

let f_survival_probability f d1 d2 =
  match classify_float f with
  | FP_nan -> nan
  | FP_infinite -> if f > 0.0 then 0.0 else nan
  | _ ->
      if f < 0.0 || d1 <= 0 || d2 <= 0 then nan
      else
        let d1f = float_of_int d1 in
        let d2f = float_of_int d2 in
        let x = 1.0 /. (1.0 +. ((d2f /. d1f) /. f)) in
        1.0 -. regularized_beta x (d1f /. 2.0) (d2f /. 2.0)

let fit_order a b =
  let by_bic = compare a.bic b.bic in
  if by_bic <> 0 then by_bic
  else
    let by_aic = compare a.aic b.aic in
    if by_aic <> 0 then by_aic else compare a.rss b.rss

let coefficient_of_variation values =
  match values with
  | [] -> None
  | _ ->
      let n = List.length values in
      let n_float = float_of_int n in
      let mean = List.fold_left ( +. ) 0.0 values /. n_float in
      if abs_float mean <= epsilon || not (is_finite mean) then None
      else
        let variance =
          List.fold_left
            (fun total value ->
              let centered = value -. mean in
              total +. (centered *. centered))
            0.0 values
          /. n_float
        in
        if variance < 0.0 || not (is_finite variance) then None
        else Some (sqrt variance /. abs_float mean)

let lower_polynomial_value coefficients degree problem_size =
  if degree <= 0 then 0.0
  else eval_polynomial_coefficients (degree - 1) coefficients ~problem_size

let leading_coefficient_stability samples coefficients degree basis =
  let ratios =
    List.filter_map
      (fun s ->
        let denominator = basis s.problem_size in
        if denominator <= epsilon || not (is_finite denominator) then None
        else
          let lower_terms = lower_polynomial_value coefficients degree s.problem_size in
          let ratio = (s.time -. lower_terms) /. denominator in
          if is_finite ratio then Some ratio else None)
      samples
  in
  if List.length ratios < 3 then None else coefficient_of_variation ratios

let quasi_polynomial_ratio_diagnostic samples degree polynomial_coefficients
    quasi_polynomial_coefficients =
  let polynomial_basis problem_size = problem_size ** float_of_int degree in
  let quasi_polynomial_basis problem_size =
    (problem_size ** float_of_int degree) *. log problem_size
  in
  let polynomial_stability =
    leading_coefficient_stability samples polynomial_coefficients degree polynomial_basis
  in
  let quasi_polynomial_stability =
    leading_coefficient_stability samples quasi_polynomial_coefficients degree quasi_polynomial_basis
  in
  match (polynomial_stability, quasi_polynomial_stability) with
  | Some polynomial_cv, Some quasi_polynomial_cv ->
      let scale = max (abs_float polynomial_cv) (abs_float quasi_polynomial_cv) in
      if
        abs_float (polynomial_cv -. quasi_polynomial_cv)
        <= (epsilon *. max 1.0 scale)
      then None
      else if quasi_polynomial_cv < polynomial_cv then
        Some (`QuasiPolynomial, polynomial_cv, quasi_polynomial_cv)
      else Some (`Polynomial, polynomial_cv, quasi_polynomial_cv)
  | _ -> None

let polynomial_quasi_pair left right =
  match (polynomial_degree left, quasi_polynomial_degree right) with
  | Some polynomial_degree, Some quasi_polynomial_degree
    when polynomial_degree = quasi_polynomial_degree ->
      Some (polynomial_degree, left, right)
  | _ -> (
      match (quasi_polynomial_degree left, polynomial_degree right) with
      | Some quasi_polynomial_degree, Some polynomial_degree
        when polynomial_degree = quasi_polynomial_degree ->
          Some (polynomial_degree, right, left)
      | _ -> None )

let apply_polynomial_quasi_diagnostic samples left right base =
  if abs_float (left.bic -. right.bic) > close_model_bic_delta then base
  else
    match polynomial_quasi_pair left.model right.model with
    | None -> base
    | Some (degree, polynomial_model, quasi_polynomial_model) -> (
        let polynomial_parameters =
          if polynomial_degree left.model = Some degree then left.parameters else right.parameters
        in
        let quasi_polynomial_parameters =
          if quasi_polynomial_degree left.model = Some degree then left.parameters
          else right.parameters
        in
        let polynomial_coefficients =
          coefficients_from_parameters polynomial_coefficient_name degree polynomial_parameters
        in
        let quasi_polynomial_coefficients =
          coefficients_from_parameters
            (quasi_polynomial_coefficient_name degree)
            degree quasi_polynomial_parameters
        in
        match
          quasi_polynomial_ratio_diagnostic samples degree polynomial_coefficients
            quasi_polynomial_coefficients
        with
        | None -> base
        | Some (winner, polynomial_cv, quasi_polynomial_cv) ->
            {
              base with
              winner =
                (match winner with
                | `Polynomial -> polynomial_model
                | `QuasiPolynomial -> quasi_polynomial_model);
              note =
                Printf.sprintf
                  "polynomial/quasi-polynomial ratio-stability diagnostic \
                   (polynomial CV=%.5g, quasi-polynomial CV=%.5g)"
                  polynomial_cv quasi_polynomial_cv;
            } )

let is_nested_model simpler richer =
  match (simpler, richer) with
  | Constant, Logarithmic | Constant, PowerLaw | Constant, Exponential -> true
  | Constant, model -> (
      match (polynomial_degree model, quasi_polynomial_degree model) with
      | Some _, _ | _, Some _ -> true
      | None, None -> false )
  | _ -> (
      match (polynomial_degree simpler, polynomial_degree richer) with
      | Some simpler_degree, Some richer_degree -> simpler_degree < richer_degree
      | _ -> (
          match (polynomial_degree simpler, quasi_polynomial_degree richer) with
          | Some simpler_degree, Some richer_degree -> simpler_degree < richer_degree
          | _ -> false ) )

let compare_fits ?(alpha = 0.05) ?samples left right =
  let bic_winner = if fit_order left right <= 0 then left.model else right.model in
  let n_ok = left.observations = right.observations in
  let k_left = parameter_count left.model in
  let k_right = parameter_count right.model in
  let base =
    {
      left = left.model;
      right = right.model;
      winner = bic_winner;
      f_statistic = None;
      p_value = None;
      significant = false;
      note = "non-nested or equal-size models; winner selected by BIC";
    }
  in
  let base =
    match samples with
    | Some samples when n_ok && List.length samples = left.observations ->
        apply_polynomial_quasi_diagnostic samples left right base
    | Some _ | None -> base
  in
  if not n_ok then { base with note = "fits have different observation counts; winner selected by BIC" }
  else if k_left = k_right then base
  else
    let simpler, richer = if k_left < k_right then (left, right) else (right, left) in
    if not (is_nested_model simpler.model richer.model) then
      { base with note = "non-nested models with different parameter counts; winner selected by BIC" }
    else
      let improvement = simpler.rss -. richer.rss in
      let rss_scale = max (abs_float simpler.rss) (abs_float richer.rss) in
      let residual_tolerance =
        match samples with Some samples -> residual_noise_floor samples | None -> 0.0
      in
      let improvement_tolerance = max (epsilon *. rss_scale) residual_tolerance in
      if improvement <= improvement_tolerance then
        {
          base with
          winner = simpler.model;
          note = "richer model does not materially reduce residual error; simpler model selected";
        }
      else
        let d1 = parameter_count richer.model - parameter_count simpler.model in
        let d2 = richer.degrees_of_freedom in
        if d2 <= 0 then
          { base with note = "not enough residual degrees of freedom for F test; winner selected by BIC" }
        else
          let f_statistic, p_value =
            if richer.rss = 0.0 then (infinity, 0.0)
            else
              let numerator = improvement /. float_of_int d1 in
              let denominator = richer.rss /. float_of_int d2 in
              let f_statistic = numerator /. denominator in
              (f_statistic, f_survival_probability f_statistic d1 d2)
          in
          let significant = is_finite p_value && p_value < alpha in
          {
            left = left.model;
            right = right.model;
            winner = (if significant then richer.model else simpler.model);
            f_statistic = Some f_statistic;
            p_value = Some p_value;
            significant;
            note = "extra-sum-of-squares F test for nested models";
          }

let chow_test ?(alpha = 0.05) restricted unrestricted = compare_fits ~alpha restricted unrestricted

let pairwise_comparisons ?(alpha = 0.05) ?samples ?(across_only = false) fits =
  let include_pair left right =
    (not across_only) || not (same_complexity_class left.model right.model)
  in
  let rec loop = function
    | [] | [ _ ] -> []
    | x :: xs ->
        let comparisons =
          xs
          |> List.filter (include_pair x)
          |> List.map (compare_fits ~alpha ?samples x)
        in
        comparisons @ loop xs
  in
  loop fits

let model_degree_for_order = function
  | Polynomial degree | QuasiPolynomial degree -> degree
  | Constant | Logarithmic | PowerLaw | Exponential -> 0

let fit_class_and_degree_order left right =
  let by_class = compare (complexity_class left.model) (complexity_class right.model) in
  if by_class <> 0 then by_class
  else compare (model_degree_for_order left.model) (model_degree_for_order right.model)

let adjacent_within_class_comparisons ?(alpha = 0.05) ?samples fits =
  let sorted_fits = List.sort fit_class_and_degree_order fits in
  let rec loop acc = function
    | left :: (right :: _ as rest) ->
        let acc =
          if same_complexity_class left.model right.model then
            compare_fits ~alpha ?samples left right :: acc
          else acc
        in
        loop acc rest
    | [] | [ _ ] -> List.rev acc
  in
  loop [] sorted_fits

let distinct_problem_size_count samples =
  samples
  |> List.map (fun sample -> sample.problem_size)
  |> List.sort_uniq compare |> List.length

let max_identifiable_polynomial_degree samples =
  min (List.length samples - 2) (distinct_problem_size_count samples - 1)

let unique_fits_by_model fits =
  let rec loop seen acc = function
    | [] -> List.rev acc
    | fitted :: rest ->
        if List.exists (fun model -> model = fitted.model) seen then loop seen acc rest
        else loop (fitted.model :: seen) (fitted :: acc) rest
  in
  loop [] [] fits

let included_degrees ~max_degree degrees =
  degrees
  |> List.filter (fun degree -> degree >= 1 && degree <= max_degree)
  |> List.sort_uniq compare

let selected_polynomial_fit ?(alpha = 0.05) ?(include_degrees = []) samples
    constant_fit =
  let candidates = ref [] in
  let significant_improvement simpler richer =
    let comparison = compare_fits ~alpha ~samples simpler richer in
    comparison.significant && comparison.winner = richer.model
  in
  let max_degree = max_identifiable_polynomial_degree samples in
  let candidate degree =
    List.find_opt
      (fun fitted -> polynomial_degree fitted.model = Some degree)
      !candidates
  in
  let fit_polynomial degree =
    match candidate degree with
    | Some fitted -> Ok fitted
    | None ->
        let model = polynomial degree in
        match fit model samples with
        | Ok fitted ->
            candidates := fitted :: !candidates;
            Ok fitted
        | Error message -> Error (string_of_complexity model ^ ": " ^ message)
  in
  let rec search_higher_degree previous degree =
    if degree > max_degree then Ok previous
    else
      match fit_polynomial degree with
      | Error _ -> Ok previous
      | Ok current when significant_improvement previous current ->
          search_higher_degree current (degree + 1)
      | Ok _ -> Ok previous
  in
  let lower_degree_choice linear_fit quadratic_fit =
    if significant_improvement linear_fit quadratic_fit then Some quadratic_fit
    else if significant_improvement constant_fit linear_fit then Some linear_fit
    else None
  in
  let* selected =
    if max_degree < 1 then Ok None
    else
      match fit_polynomial 1 with
      | Error _ -> Ok None
      | Ok linear_fit ->
          if max_degree = 1 then
            Ok (if significant_improvement constant_fit linear_fit then Some linear_fit else None)
          else
            match fit_polynomial 2 with
            | Error _ ->
                Ok
                  (if significant_improvement constant_fit linear_fit then Some linear_fit else None)
            | Ok quadratic_fit ->
                let* searched_fit = search_higher_degree quadratic_fit 3 in
                Ok
                  (match polynomial_degree searched_fit.model with
                  | Some degree when degree > 2 -> Some searched_fit
                  | _ -> lower_degree_choice linear_fit quadratic_fit)
  in
  let forced_fits =
    include_degrees
    |> included_degrees ~max_degree
    |> List.filter_map (fun degree ->
           match fit_polynomial degree with Ok fitted -> Some fitted | Error _ -> None)
  in
  let selected_fits = match selected with None -> [] | Some fitted -> [ fitted ] in
  Ok (selected, unique_fits_by_model (selected_fits @ forced_fits), List.rev !candidates)

let selected_quasi_polynomial_fit ?(alpha = 0.05) ?(include_degrees = []) samples
    constant_fit polynomial_fit =
  let sample_max_degree = max_identifiable_polynomial_degree samples in
  let max_degree =
    match polynomial_fit with
    | Some polynomial_fit -> (
        match polynomial_degree polynomial_fit.model with
        | Some degree -> min sample_max_degree degree
        | None -> min sample_max_degree 1 )
    | None -> min sample_max_degree 1
  in
  let candidates = ref [] in
  let candidate degree =
    List.find_opt
      (fun fitted -> quasi_polynomial_degree fitted.model = Some degree)
      !candidates
  in
  let fit_quasi_polynomial degree =
    match candidate degree with
    | Some fitted -> Ok fitted
    | None ->
        let model = quasi_polynomial degree in
        match fit model samples with
        | Ok fitted ->
            candidates := fitted :: !candidates;
            Ok fitted
        | Error message -> Error (string_of_complexity model ^ ": " ^ message)
  in
  let rec fit_degrees degree =
    if degree > max_degree then Ok ()
    else
      let* () =
        match fit_quasi_polynomial degree with Ok _ -> Ok () | Error _ -> Ok ()
      in
      fit_degrees (degree + 1)
  in
  let* () = fit_degrees 1 in
  let normal_candidates = List.rev !candidates in
  let* selected =
    match List.sort fit_order normal_candidates with
    | [] -> Ok None
    | best :: _ ->
        let comparison = compare_fits ~alpha constant_fit best in
        if not (comparison.significant && comparison.winner = best.model) then Ok None
        else
          match quasi_polynomial_degree best.model with
          | None -> Ok (Some best)
          | Some degree -> (
              match fit (polynomial degree) samples with
              | Error _ -> Ok (Some best)
              | Ok polynomial_fit ->
                  let comparison = compare_fits ~alpha ~samples polynomial_fit best in
                  Ok (if comparison.winner = polynomial_fit.model then None else Some best) )
  in
  let forced_fits =
    include_degrees
    |> included_degrees ~max_degree:sample_max_degree
    |> List.filter_map (fun degree ->
           match fit_quasi_polynomial degree with
           | Ok fitted -> Some fitted
           | Error _ -> None)
  in
  let selected_fits = match selected with None -> [] | Some fitted -> [ fitted ] in
  Ok (selected, unique_fits_by_model (selected_fits @ forced_fits), List.rev !candidates)

let string_contains haystack needle =
  let haystack_length = String.length haystack in
  let needle_length = String.length needle in
  let rec loop index =
    if needle_length = 0 then true
    else if index + needle_length > haystack_length then false
    else if String.sub haystack index needle_length = needle then true
    else loop (index + 1)
  in
  loop 0

let skippable_candidate_error message =
  string_contains message "rank deficient"
  || string_contains message "singular"
  || string_contains message "non-finite"
  || string_contains message "nonlinear regression failed"

let insert_selected_fits fixed_fits polynomial_fits quasi_polynomial_fits =
  let selected_fits = unique_fits_by_model (polynomial_fits @ quasi_polynomial_fits) in
  match (fixed_fits, selected_fits) with
  | _, [] -> fixed_fits
  | constant_fit :: logarithmic_fit :: rest, selected_fits ->
      constant_fit :: logarithmic_fit :: (selected_fits @ rest)
  | _ -> fixed_fits @ selected_fits

let estimate ?(alpha = 0.05) ?(include_polynomial_degrees = [])
    ?(include_quasi_polynomial_degrees = []) samples =
  let rec fit_all acc = function
    | [] -> Ok (List.rev acc)
    | model :: rest -> (
        match fit model samples with
        | Ok fitted -> fit_all (fitted :: acc) rest
        | Error message when acc <> [] && skippable_candidate_error message -> fit_all acc rest
        | Error message -> Error (string_of_complexity model ^ ": " ^ message))
  in
  let* fixed_fits = fit_all [] fixed_models in
  match fixed_fits with
  | [] -> Error "no candidate models"
  | constant_fit :: _ ->
      let* polynomial_fit, polynomial_fits, polynomial_candidates =
        selected_polynomial_fit ~alpha ~include_degrees:include_polynomial_degrees samples
          constant_fit
      in
      let* quasi_polynomial_fit, quasi_polynomial_fits, quasi_polynomial_candidates =
        selected_quasi_polynomial_fit ~alpha
          ~include_degrees:include_quasi_polynomial_degrees samples constant_fit
          polynomial_fit
      in
      let fits = insert_selected_fits fixed_fits polynomial_fits quasi_polynomial_fits in
      let within_comparisons =
        adjacent_within_class_comparisons ~alpha ~samples
          (polynomial_candidates @ quasi_polynomial_candidates)
      in
      match List.sort fit_order fits with
      | [] -> Error "no candidate models"
      | best :: _ ->
          Ok
            {
              fits;
              best;
              comparisons = pairwise_comparisons ~alpha ~samples ~across_only:true fits;
              within_comparisons;
            }

module Holdout = Holdout.Make (struct
  type nonrec complexity = complexity

  type nonrec sample = sample = {
    problem_size : float;
    time : float;
  }

  type nonrec fit = fit = {
    model : complexity;
    parameters : parameter list;
    rss : float;
    r_squared : float;
    aic : float;
    bic : float;
    degrees_of_freedom : int;
    observations : int;
  }

  type nonrec comparison = comparison = {
    left : complexity;
    right : complexity;
    winner : complexity;
    f_statistic : float option;
    p_value : float option;
    significant : bool;
    note : string;
  }

  type nonrec estimate = estimate = {
    fits : fit list;
    best : fit;
    comparisons : comparison list;
    within_comparisons : comparison list;
  }

  let predict = predict
  let estimate ?alpha samples = estimate ?alpha samples
  let string_of_complexity = string_of_complexity
end)
