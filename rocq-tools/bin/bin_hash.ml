let panic : ('a, unit, string, 'd) format4 -> 'a = fun fmt ->
  Printf.ksprintf (fun s -> Printf.eprintf "%s\n%!" s; exit 1) fmt

let bin_path : string -> string = fun bin_name ->
  let cmd = Printf.sprintf "which %s" bin_name in
  let ic = Unix.open_process_in cmd in
  let hash = In_channel.input_line ic in
  match (hash, Unix.close_process_in ic) with
  | (Some hash, Unix.WEXITED 0) -> String.trim hash
  | _ -> panic "Error: [%s] did not behave as expected." cmd

let _ =
  let (lang, val_name, bin_name) =
    match Sys.argv with
    | [|_; "--ocaml"; val_name; bin_name|] -> (`OCaml, val_name, bin_name)
    | [|_; "--rocq" ; val_name; bin_name|] -> (`Rocq , val_name, bin_name)
    | [|_; "--sh"   ; val_name; bin_name|] -> (`Sh   , val_name, bin_name)
    | _                                    ->
        panic "Usage: %s (--ocaml | --rocq | --sh) VALUE_NAME BIN_NAME" Sys.argv.(0)
  in
  let path = bin_path bin_name in
  let hash = Digest.MD5.(to_hex (file path)) in
  match lang with
  | `OCaml ->
      Printf.printf "let %s = %S\n%!" val_name hash
  | `Rocq  ->
      Printf.printf "Require Import PrimString.\n\n";
      Printf.printf "Definition %s := %S%%pstring.\n%!" val_name hash
  | `Sh    ->
      Printf.printf "%s=%S\n%!" val_name hash
