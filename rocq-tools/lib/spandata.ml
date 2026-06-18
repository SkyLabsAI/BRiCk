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

open Extra

module Data = struct
  type t = {
    count : int;
    instr : int;
  }

  let (+) : t -> t -> t = fun data1 data2 ->
    let count = data1.count + data2.count in
    let instr = data1.instr + data2.instr in
    {count; instr}
end

module Span = struct
  type t = {
    name   : string;
    status : string option;
  }

  let of_log_span : Log.span -> t = fun span ->
    let name = span.Log.name in
    let status =
      match List.assoc_opt "status" span.Log.metadata with
      | None             -> None
      | Some(`String(s)) -> Some(s)
      | Some(_         ) ->
      panic "Error: unexpected JSON value for [status] span metadata."
    in
    {name; status}

  let of_string : string -> t = fun s ->
    match String.split_on_char '+' s with
    | [name]         -> {name; status = None}
    | [name; status] -> {name; status = Some(status)}
    | _              ->
    panic "Error: %S cannot be parsed as a span/status pair." s

  let to_string : t -> string = fun span ->
    match span.status with
    | None         -> span.name
    | Some(status) -> span.name ^ "+" ^ status
end

module Key = struct
  type t = {
    span_path : Span.t list;
    span      : Span.t;
  }

  let compare = Stdlib.compare
end

module M = Map.Make(Key)

type map = Data.t M.t

let accumulate : Key.t -> Data.t -> map -> map = fun key new_data m ->
  let combine data =
    match data with
    | None       -> Some(new_data)
    | Some(data) -> Some(Data.(data + new_data))
  in
  M.update key combine m

let aggregate_filter : (Key.t -> Key.t option) -> map -> map = fun f m ->
  let insert key data m =
    match f key with
    | Some(key) -> accumulate key data m
    | None      -> m
  in
  M.fold insert m M.empty

let add_log_data : Log.t -> map -> map = fun log m ->
  let m = ref m in
  let handle_span spans span _ =
    let instr =
      let c0 =
        match List.assoc_opt "c0" span.Log.metadata with
        | None     -> panic "Error: no instruction count field (c0)."
        | Some(c0) ->
        match c0 with
        | `Int(c0) -> c0
        | _        -> panic "Error: ill-typed instruction count field (c0)."
      in
      let c1 =
        match List.assoc_opt "c1" span.Log.metadata with
        | None     -> panic "Error: no instruction count field (c1)."
        | Some(c1) ->
        match c1 with
        | `Int(c1) -> c1
        | _        -> panic "Error: ill-typed instruction count field (c1)."
      in
      c1 - c0
    in
    let span_path = List.rev_map Span.of_log_span spans in
    let span = Span.of_log_span span in
    m := accumulate Key.{span_path; span} Data.{instr; count = 1} !m
  in
  Log.iter (fun _ _ -> ()) handle_span log; !m

let add_log_file : string -> map -> map = fun file m ->
  let log =
    let open Yojson in
    try Basic.from_file file with
    | Json_error(s) -> panic "Error: bad profiling data, %s." s
    | Sys_error(s)  -> panic "Error: %s." s
  in
  let log =
    try Log.of_json log with Log.Error(msg) ->
      panic "Error: %s." msg
  in
  add_log_data log m

let add_csv_file : string -> map -> map = fun file m ->
  let add_line m line =
    match List.map String.trim (String.split_on_char ',' line) with
    | [span_path; span; count; instr] ->
        let span_path =
          let span_path = String.split_on_char ':' span_path in
          List.map Span.of_string span_path
        in
        let span = Span.of_string span in
        let count = int_of_string count in
        let instr = int_of_string instr in
        accumulate Key.{span_path; span} Data.{count; instr} m
    | [""]                            -> m
    | _                               -> panic "Invalid CSV."
  in
  try
    In_channel.with_open_text file @@ fun ic ->
    ignore (In_channel.input_line ic); (* Drop header line. *)
    let rec loop m =
      match In_channel.input_line ic with
      | Some(line) -> loop (add_line m line)
      | None       -> m
    in
    loop m
  with Sys_error(s) -> panic "Error: %s." s

let output_csv : Out_channel.t -> map -> unit = fun oc m ->
  Printf.fprintf oc "Span path,Span,Count,Instructions\n";
  let print_line Key.{span_path; span} Data.{count; instr} =
    let span_path = String.concat ":" (List.map Span.to_string span_path) in
    let span = Span.to_string span in
    Printf.fprintf oc "%s,%s,%i,%i\n" span_path span count instr
  in
  M.iter print_line m
