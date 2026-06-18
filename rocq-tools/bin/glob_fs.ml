(*
 * Copyright (C) 2023-2024 BlueRock Security, Inc.
 *
 * This library is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; version 2.1.
 *
 * This library is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public License
 * for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this library; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 *)

open Rocq_tools
open Rocq_tools.Extra

let of_file : file:string -> string = fun ~file ->
  In_channel.with_open_text file In_channel.input_all

let to_file : data:string -> file:string -> unit = fun ~data ~file ->
  Out_channel.with_open_text file @@ fun oc ->
  Out_channel.output_string oc data

let glob_ls glob =
  let keys = Globfs.list_keys ~glob in
  let print_file key =
    let key = Globfs.Key.to_string ~key in
    Printf.printf "%s:%s\n" glob key
  in
  List.iter print_file keys; Printf.printf "%!"

let parse_glob_key cmd glob =
  match String.split_on_char ':' glob with
  | [glob]      -> (glob, None)
  | [glob; key] -> (glob, Some(Globfs.Key.of_string key))
  | _           -> panic "Ill-formed argument %S to command %s." glob cmd

let glob_cat glob =
  let (glob, key) = parse_glob_key "cat" glob in
  let data =
    match key with
    | None      -> Globfs.glob_data ~glob
    | Some(key) -> Globfs.find ~glob ~key
  in
  Printf.printf "%s%!" data

let glob_cp from dest =
  let (from, from_key) = parse_glob_key "cp" from in
  let (dest, dest_key) = parse_glob_key "cp" dest in
  match (from_key, dest_key) with
  | (None          , None          ) ->
      let data = of_file ~file:from in
      to_file ~data ~file:dest
  | (Some(from_key), None          ) ->
      let data = Globfs.find ~glob:from ~key:from_key in
      to_file ~data ~file:dest
  | (None          , Some(dest_key)) ->
      Globfs.append_gen ~glob:dest ~key:dest_key ~file:from
  | (Some(from_key), Some(dest_key)) ->
      let data = Globfs.find ~glob:from ~key:from_key in
      Globfs.append_data ~glob:dest ~key:dest_key ~data

let glob_extract glob =
  let (glob, key) = parse_glob_key "cat" glob in
  match key with
  | None      -> Globfs.extract_all ~glob
  | Some(key) -> Globfs.extract_key ~glob ~key

let glob_clear glob =
  Globfs.clear ~glob

let usage ~fail =
  let line fmt = Printf.eprintf (fmt ^^ "\n") in
  line "Usage: %s CMD [ARGS]" Sys.argv.(0);
  line "Available commands (CMD):";
  line "  help\t\t\t: shows this help message.";
  line "  ls GLOB\t\t: lists the files embedded in GLOB.";
  line "  cat GLOB\t\t: lists the contents of the original glob file only.";
  line "  cat GLOB:KEY\t\t: lists the contents of file KEY in GLOB.";
  line "  cp GLOB:KEY FILE\t: extracts GLOB.KEY from GLOB to FILE.";
  line "  cp FILE GLOB:KEY\t: embeds FILE as GLOB.KEY into GLOB.";
  line "  extract GLOB\t\t: extracts all files from GLOB.";
  line "  extract GLOB:KEY\t: extracts the file KEY in GLOB.";
  line "  clear GLOB\t\t: restores GLOB to its original state.";
  if fail then panic "Invalid command line arguments."

let main () =
  match Sys.argv with
  | [|_; "help"               |] -> usage ~fail:false
  | [|_; "ls"     ; glob      |] -> glob_ls glob
  | [|_; "cat"    ; glob      |] -> glob_cat glob
  | [|_; "cp"     ; from; dest|] -> glob_cp from dest
  | [|_; "extract"; glob      |] -> glob_extract glob
  | [|_; "clear"  ; glob      |] -> glob_clear glob
  | _                            -> usage ~fail:true

let _ =
  try main () with
  | Invalid_argument(msg)
  | Sys_error(msg) -> panic "%s" msg
  | Not_found -> panic "File key not found."
  | Globfs.Ill_formed -> panic "Ill-formed file embedding."
