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

let normalize_dir_path : string -> string = fun dir ->
  let restore_cwd =
    let cwd = Sys.getcwd () in
    fun () -> Sys.chdir cwd
  in
  try Sys.chdir dir; let res = Sys.getcwd () in restore_cwd (); res
  with Sys_error _ -> restore_cwd (); dir

type file_path = string

let invalid_arg fmt = Extra.failwith ~fail:invalid_arg fmt

let check_file file =
  try
    if Sys.is_directory file then
      invalid_arg "File expected, found directory %S." file
  with Sys_error(_) ->
    invalid_arg "File not found %S." file

let check_glob glob =
  check_file glob;
  if Filename.extension glob <> ".glob" then
    invalid_arg "Glob file expected, found %S." glob

module Key = struct
  type t = string

  let of_string s =
    let items = String.split_on_char '.' s in
    if items = [] then invalid_arg "Empty key.";
    let check_item item =
      if String.length item = 0 then invalid_arg "Empty key member.";
      let check_char i c =
        match c with
        | 'a'..'z' | 'A'..'Z'  -> ()
        | '0'..'9' when i <> 0 -> ()
        | _                    -> invalid_arg "Bad key character %C." c
      in
      String.iteri check_char item
    in
    List.iter check_item items; s

  let to_string ~key = key

  let of_file ~glob ~file =
    check_glob glob;
    let glob_dir = normalize_dir_path (Filename.dirname glob) in
    let file_dir = normalize_dir_path (Filename.dirname file) in
    if glob_dir <> file_dir then
      invalid_arg "%S and %S are not in the same directory." glob file;
    let glob_base = Filename.basename glob in
    let file_base = Filename.basename file in
    if not (String.starts_with ~prefix:glob_base file_base) then
      invalid_arg "The path of %S is not based on %S." file glob;
    let glob_base_len = String.length glob_base in
    let file_base_len = String.length file_base in
    if glob_base_len = file_base_len then
      invalid_arg "%S and %S are the same file." glob file;
    if String.get file_base glob_base_len <> '.' then
      invalid_arg "%S does not extend %S with an extension." file glob;
    let key_len = String.length file_base - String.length glob_base - 1 in
    String.sub file_base (String.length glob_base + 1) key_len

  let to_file ~glob ~key =
    check_glob glob; glob ^ "." ^ key
end

exception Ill_formed

module Data : sig
  type t

  (* Encoding / Decoding *)
  val encode : string -> t
  val decode : t -> string

  (* Parsing / Printing. *)
  val to_string : t -> string
  val of_string : string -> t
end = struct
  type t = Base64.t

  let encode s =
    try Base64.encode (Zip.compress ~level:9 s) with
    | Zip.Error(_) -> raise Ill_formed

  let decode data =
    try Zip.decompress (Base64.decode data) with
    | Zip.Error(_) -> raise Ill_formed

  let to_string = Base64.to_string
  let of_string = Base64.of_string
end

(* Representation of a line of a glob file (standard of embedded file). *)
module GlobLine = struct
  type t =
    | Standard of string
    | File of {key : Key.t; data : Data.t}

  let prefix : string =
    Printf.sprintf "R%i:%i glob.hack." max_int max_int

  let prefix_len : int =
    String.length prefix

  let output : Out_channel.t -> t -> unit = fun oc line ->
    match line with
    | Standard(s)       -> Printf.fprintf oc "%s\n" s
    | File({key; data}) ->
        let data = Data.to_string data in
        Printf.fprintf oc "%s%s <> :::'%s' not\n" prefix key data

  let input : In_channel.t -> t = fun ic ->
    let line = Stdlib.input_line ic in
    let len = String.length line in
    match String.starts_with ~prefix line with
    | false -> Standard(line)
    | true  ->
    try
      let sep = String.index line '<' in
      let key = String.sub line prefix_len (sep - prefix_len - 1) in
      let data = String.sub line (sep + 7) (len - sep - 12) in
      let data = Data.of_string data in
      File({key; data})
    with Not_found | Invalid_argument(_) -> raise Ill_formed
end

let append_data ~glob ~key ~data =
  check_glob glob;
  Out_channel.with_open_gen [Out_channel.Open_append] 0 glob @@ fun oc ->
  let data = Data.encode data in
  GlobLine.(output oc (File({key; data})))

let append_gen ~glob ~key ~file =
  check_file glob; check_file file;
  let data = In_channel.with_open_text file In_channel.input_all in
  append_data ~glob ~key ~data

let append ~glob ~file =
  let key = Key.of_file ~glob ~file in
  append_gen ~glob ~key ~file

let iter ~glob f g =
  check_file glob;
  In_channel.with_open_text glob @@ fun ic ->
  try while true do
    match GlobLine.input ic with
    | Standard(line)    -> f ~line
    | File({key; data}) -> g ~key ~data
  done with End_of_file -> ()

let glob_data ~glob =
  let buf = Buffer.create 73 in
  let add_line ~line = Buffer.add_string buf line; Buffer.add_char buf '\n' in
  iter ~glob add_line (fun ~key:_ ~data:_ -> ());
  Buffer.contents buf

let clear ~glob =
  let data = glob_data ~glob in
  Out_channel.with_open_text glob @@ fun oc ->
  Out_channel.output_string oc data

let list_keys ~glob =
  let keys = ref [] in
  let add_key ~key ~data:_ = keys := key :: !keys in
  iter ~glob (fun ~line:_ -> ()) add_key;
  List.rev !keys

module SMap = Map.Make(String)

let to_map ~glob =
  let map = ref SMap.empty in
  let insert ~key ~data = map := SMap.add key data !map in
  iter ~glob (fun ~line:_ -> ()) insert; !map

let find ~glob ~key =
  Data.decode (SMap.find key (to_map ~glob))

let cat_key oc ~glob ~key =
  Out_channel.output_string oc (find ~glob ~key)

let extract_key ~glob ~key =
  let file = Key.to_file ~glob ~key in
  Out_channel.with_open_text file @@ fun oc ->
  cat_key oc ~glob ~key

let extract ~glob ~file =
  let key = Key.of_file ~glob ~file in
  extract_key ~glob ~key

let extract_all ~glob =
  let map = to_map ~glob in
  let write_file key data =
    let file = Key.to_file ~glob ~key in
    let data = Data.decode data in
    Out_channel.with_open_text file @@ fun oc ->
    Out_channel.output_string oc data
  in
  SMap.iter write_file map
