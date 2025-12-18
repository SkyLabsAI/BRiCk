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

type mode = Binary | Text

module IMap = Map.Make(Int)

type glob_file = {
  standard : string list;
  fields : (mode * Base64.t) IMap.t;
}

let fold_fields f glob acc =
  IMap.fold (fun key (mode, value) -> f ~key ~mode ~value) glob.fields acc

let iter_fields f glob =
  IMap.iter (fun key (mode, value) -> f ~key ~mode ~value) glob.fields

let find_field ~key glob =
  if key < 0 then invalid_arg "negative key";
  IMap.find key glob.fields

let add_field ~key ~mode ~value glob =
  if key < 0 then invalid_arg "negative key";
  let value = Base64.encode value in
  {glob with fields = IMap.add key (mode, value) glob.fields}

let remove_field ~key glob =
  if key < 0 then invalid_arg "negative key";
  {glob with fields = IMap.remove key glob.fields}

module Key : sig
  type t = string

  val of_int : int -> t
  val to_int : t -> int option

  val max_key : t
end = struct
  type t = string

  let of_int : int -> t = fun i ->
    if i < 0 then raise (Invalid_argument "Key.of_int");
    Printf.sprintf "1%019i" i

  let to_int : t -> int option = fun s ->
    let s = String.sub s 1 (String.length s - 1) in
    try Some(int_of_string s) with Failure(_) -> None

  let max_key : t = of_int max_int
end

type glob_line =
  | Standard of string
  | Field of {key : int; mode : mode; value : Base64.t}

let output : Out_channel.t -> glob_line -> unit = fun oc line ->
  let output_mode oc m =
    match m with
    | Text -> ()
    | Binary -> output_string oc "bin"
  in
  match line with
  | Standard(s) ->
      Printf.fprintf oc "%s\n" s
  | Field(e) ->
      Printf.fprintf oc "R%s:%s sl.perf <%a> :::'%s' not\n"
        (Key.of_int e.key) Key.max_key output_mode e.mode
        (Base64.to_string e.value)

exception Bad_glob_file

let input : In_channel.t -> glob_line = fun ic ->
  let line = Stdlib.input_line ic in
  let len = String.length line in
  if len < 1 then raise Bad_glob_file;
  if line.[0] <> 'R' then Standard(line) else
  match String.index_opt line ' ' with
  | None -> Standard(line)
  | Some(si1) ->
  match String.index_from_opt line (si1+1) ' ' with
  | None -> Standard(line)
  | Some(si2) ->
  match String.index_opt line ':' with
  | None -> Standard(line)
  | Some(ci) ->
  let name = String.sub line (si1 + 1) (si2 - si1 - 1) in
  if name <> "sl.perf" then Standard(line) else
  match Key.to_int (String.sub line 1 (ci - 1)) with
  | None -> raise Bad_glob_file
  | Some(key) ->
  let (mode, data) =
    match String.split_on_char ' ' line with
    | [_; _; mode; data; _] -> (mode, data)
    | _ -> raise Bad_glob_file
  in
  let len = String.length data in
  if len < 6 then raise Bad_glob_file;
  let mode =
    match mode with
    | "<bin>" -> Binary
    | "<>" -> Text
    | _ -> raise Bad_glob_file
  in
  let value = Base64.of_string (String.sub data 4 (len - 5)) in
  Field({key; mode; value})

let read_glob_file ~allow_fields path =
  let ic = In_channel.open_text path in
  let standard = ref [] in
  let fields = ref IMap.empty in
  try
    while true do
      match input ic with
      | Standard(s) -> standard := s :: !standard
      | Field(_) when not allow_fields -> raise Bad_glob_file
      | Field(e) -> fields := IMap.add e.key (e.mode, e.value) !fields
    done; assert false
  with
  | End_of_file ->
      In_channel.close_noerr ic;
      let standard = !standard in
      let fields = !fields in
      {standard; fields}
  | e ->
      In_channel.close_noerr ic;
      raise e

let write_glob_file path {standard; fields} =
  let oc = Out_channel.open_text path in
  let add s = output oc (Standard(s)) in
  List.iter add standard;
  let add key (mode, value) = output oc (Field({key; mode; value})) in
  IMap.iter add fields;
  Out_channel.close_noerr oc

let write_fields ~assume_new path mappings =
  let check (key, _, _) = if key < 0 then invalid_arg "negative key" in
  List.iter check mappings;
  if assume_new then
    let oc = Out_channel.open_gen [Out_channel.Open_append] 0 path in
    let output (key, mode, value) =
      output oc (Field({key; mode; value = Base64.encode value}))
    in
    List.iter output mappings;
    Out_channel.close_noerr oc
  else
    let glob = read_glob_file ~allow_fields:true path in
    let add glob (key, mode, value) = add_field ~key ~mode ~value glob in
    let glob = List.fold_left add glob mappings in
    write_glob_file path glob

let write_field ~assume_new path ~key ~mode ~value =
  write_fields ~assume_new path [(key, mode, value)]

let read_field path ~key =
  let {fields; _} = read_glob_file ~allow_fields:true path in
  IMap.find key fields

let read_fields path ~keys =
  let check key = if key < 0 then invalid_arg "negative key" in
  List.iter check keys;
  let {fields; _} = read_glob_file ~allow_fields:true path in
  let get key =
    let (mode, value) = IMap.find key fields in
    (key, mode, value)
  in
  List.map get keys

let read_all_fields path =
  let glob = read_glob_file ~allow_fields:true path in
  let cons ~key ~mode ~value acc = (key, mode, value) :: acc in
  List.rev (fold_fields cons glob [])
