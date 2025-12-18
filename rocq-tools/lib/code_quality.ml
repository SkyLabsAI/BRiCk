(*
 * Copyright (C) 2023-2025 BlueRock Security, Inc.
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

type pos = {
  line : int; (* Line number.  *)
  c0   : int; (* Start column. *)
  c1   : int; (* End column.   *)
}

module Warning = struct
  type t = {
    file : string;     (* File where the warning originated.     *)
    pos  : pos option; (* Optional warning position in the file. *)
    name : string;     (* Name for the warning.                  *)
    text : string;     (* Text from the warning.                 *)
    full : string;     (* Original content including headers     *)
  }

  let is_name_flaky : string -> bool =
    let re = Str.regexp {re|\b\(sl-work-timeout\|dummy\)\b|re} in
    fun name ->
    try
      let _ = Str.search_forward re name 0 in
      true
    with Not_found -> false

  let is_flaky : t -> bool = fun {name; _} ->
    is_name_flaky name

  let compare : t -> t -> int = fun w1 w2 ->
    let c = String.compare w1.name w2.name in
    if c <> 0 then c else
    let flaky = is_flaky w1 in      (* = is_flaky w2 *)
    if flaky then
      Stdlib.compare (w1.file, w1.pos) (w2.file, w2.pos) (* compare only the remaining non-text fields *)
    else
      String.compare w1.full w2.full (* just compare everything *)
end

module Error = struct
  type t = {
    file : string;
    pos  : pos option;
    text : string;
    full : string;
  }

  let compare : t -> t -> int = Stdlib.compare
end

let get_lines : In_channel.t -> (string -> 'a) -> 'a list = fun ic f ->
  let rec loop rev_lines =
    match In_channel.input_line ic with
    | None -> List.rev rev_lines
    | Some(line) -> loop (f line :: rev_lines)
  in
  loop []

type line =
  | Header of { file : string; pos: pos option; full: string (* full line *) }
  | Data of string * bool (* Is this the last warning line? *)

let normalize_path : string -> string = fun path ->
  if String.starts_with ~prefix:"./" path then
    String.sub path 2 (String.length path - 2)
  else
    path

let parse_line : string -> line = fun line ->
  try
    Scanf.sscanf line "File %S, line %i, characters %i-%i:" @@
      fun w_file line_no c0 c1 ->
    let file = normalize_path w_file in
    let pos = if line_no = 0 then None else Some({line=line_no; c0; c1}) in
    Header{file; pos; full=line}
  with
  | End_of_file
  | Scanf.Scan_failure(_) ->
    let last_warning_line =
      let re = "^.*[[][^ ]+[]]$" in
      Str.string_match (Str.regexp re) line 0
    in
    Data(line, last_warning_line)

type item =
  | Warning of Warning.t
  | Error of Error.t
  | Line of int * string

let make_warning : string -> pos option -> string -> string -> Warning.t =
    fun file pos data full ->
  let (name, text) =
    if not (String.starts_with ~prefix:"Warning:" data) then
      panic "Invalid warning (no leading  \"Warning:\").";
    let len = String.length data in
    let ibracket = String.rindex_from data (len - 1) '[' in
    let tags = String.sub data (ibracket + 1) (len - ibracket - 2) in
    let tags = String.split_on_char ',' tags in
    let text = String.sub data 9 (len - 8 - (len - ibracket) - 2) in
    (List.hd tags, String.trim text)
  in
  {file; pos; name; text; full}

let make_error : string -> pos option -> string -> string -> Error.t =
    fun file pos text full ->
  {file; pos; text; full}

type kind =
  | E (* Error *)
  | W (* Warning *)
  | U (* Unknown *)

let kind_of_prefix : string -> kind =
  fun data ->
  let data = String.trim data in
  if String.starts_with ~prefix:"Error:" data then E
  else if String.starts_with ~prefix:"Warning:" data then W
  else U                        (* TODO: panic? *)

type state = {
  kind : kind;
  file : string;
  pos : pos option;
  headers : string list;        (* reversed header(s) of the current item being parsed *)
  data : string list;           (* reversed content after the header(s) *)
}

let make_item : state -> item =
  fun {kind; file; pos; headers; data} ->
  let data = List.rev data in
  let full = List.rev_append headers data in
  let data = String.trim (String.concat "\n" data) in
  let full = String.concat "\n" full in
  match kind with
  | E -> Error (make_error file pos data full)
  | W -> Warning (make_warning file pos data full)
  | U -> assert false

let gather : ?assume_errors:bool -> line list -> item list =
  fun ?(assume_errors=true) lines ->
  let default_kind = if assume_errors then E else U in
  let rec gather i rev_items state lines =
    let gather = gather (i+1) in
    match (state, lines) with
    | (None, []) ->
        List.rev rev_items
    | (Some{kind=W; _}, []) ->
      panic "Unexpected end of warning at line %i." i
    | (Some{data=[]; _}, []) ->
      panic "File and position state without content after it in line %i." i
    | (Some{kind=U; data=_ :: _; _}, _) ->
      panic "Unknown output in line %i." i
    | (Some(s), []) ->
      let item = make_item s in
      gather (item :: rev_items) None lines
    | (None                 , Header{file; pos; full} :: lines) ->
        gather rev_items (Some{kind=default_kind; file; pos; headers=[full]; data=[]}) lines
    | (None                 , Data(line, false) :: lines) ->
        gather (Line(i, line) :: rev_items) state lines
    | (None                 , Data(_   , true ) :: _    ) ->
        panic "Dangling output at line %i." i
    | (Some({kind=U; data=[]; _} as s), Data(line, is_last_warning_line) :: lines) ->
        let kind = kind_of_prefix line in
        if kind = W && is_last_warning_line then
          let item = make_item {s with kind=W; data=[line]} in
          gather (item :: rev_items) None lines
        else
          gather rev_items (Some{s with kind; data=[line]}) lines
    | (Some({kind=E; data; _} as s), Data(line, _) :: lines) ->
        gather rev_items (Some{s with data=line :: data}) lines
    | (Some({kind=E; _} as s), Header({file=h_file; pos=h_pos; full}) :: lines) ->
      let item = make_item s in
      gather (item :: rev_items) (Some{kind=default_kind; file=h_file; pos=h_pos; headers=[full]; data=[]}) lines
    | (Some({kind=W; _} as s), Data(line, false) :: lines) ->
        gather rev_items (Some{s with data=line :: s.data}) lines
    | (Some({kind=W; _} as s), Data(line, true ) :: lines) ->
        let item = make_item {s with data=line :: s.data} in
        gather (item :: rev_items) None lines
    | (Some{kind=(W | U); _},      Header _ :: _    ) ->
        panic "Nested warning at line %i." i
  in
  gather 1 [] None lines

let parse_lines ?(assume_errors=false) lines =
  let items = gather ~assume_errors lines in
  let (lines, warnings, errors) =
    let f item (lines, warnings, errors) =
      match item with
      | Line(i, line) -> ((i, line) :: lines, warnings, errors)
      | Error(e)      -> (lines, warnings, e :: errors)
      | Warning(w)    -> (lines, w :: warnings, errors)
    in
    List.fold_right f items ([], [], [])
  in
  lines, warnings, errors
