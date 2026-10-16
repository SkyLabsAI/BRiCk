open Guesstimator.Core

let fail message = failwith message

let require condition message = if not condition then fail message

let require_complexity_round_trip model =
  let string = string_of_complexity model in
  match complexity_of_string string with
  | Some parsed ->
      require (parsed = model)
        (Printf.sprintf "expected %S to parse back to %s, got %s" string
           (string_of_complexity model) (string_of_complexity parsed))
  | None -> fail (Printf.sprintf "expected %S to parse" string)

let require_string_round_trip string =
  match complexity_of_string string with
  | Some parsed ->
      let rendered = string_of_complexity parsed in
      require (rendered = string)
        (Printf.sprintf "expected %S to render back to itself, got %S" string rendered)
  | None -> fail (Printf.sprintf "expected %S to parse" string)

let require_not_parsed string =
  match complexity_of_string string with
  | None -> ()
  | Some parsed ->
      fail
        (Printf.sprintf "expected %S not to parse, got %s" string
           (string_of_complexity parsed))

let () =
  let models =
    [
      Constant;
      Logarithmic;
      polynomial 1;
      polynomial 2;
      polynomial 7;
      quasi_polynomial 1;
      quasi_polynomial 2;
      quasi_polynomial 7;
      PowerLaw;
      Exponential;
    ]
  in
  List.iter require_complexity_round_trip models;
  List.iter require_string_round_trip (List.map string_of_complexity models);
  List.iter require_not_parsed
    [
      "";
      "linear";
      "polynomial";
      "polynomial-";
      "polynomial-0";
      "polynomial--1";
      "quasi-polynomial";
      "quasi-polynomial-";
      "quasi-polynomial-0";
      "powerlaw";
    ]
