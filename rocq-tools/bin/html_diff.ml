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

let (src_ref, data_ref, src_new, data_new) =
  match Sys.argv with
  | [|_; s1; d1; s2; d2|] -> (s1, d1, s2, d2)
  | _ -> panic "Usage: %s ref.v ref.json new.v new.json" Sys.argv.(0)

let input_file : string -> string = fun file ->
  try In_channel.with_open_text file In_channel.input_all with
  | Sys_error(msg) -> panic "Error: %s" msg

let input_data : string -> Data.t = fun file ->
  let open Data in
  try read_json file with
  | Sys_error(s)  -> panic "Error wile reading %s: %s" file s
  | Read_error(s) -> panic "Error wile reading %s: %s" file s

type diff_status =
  | Identical
  | DifferAt of int
  | TruncatedRef
  | TruncatedSrc

let diff_status : string -> string -> diff_status = fun ref src ->
  let len_ref = String.length ref in
  let len_src = String.length src in
  let rec loop i =
    match (i < len_ref, i < len_src) with
    | (false, false) -> Identical
    | (true , true ) -> if ref.[i] = src.[i] then loop (i+1) else DifferAt(i)
    | (true , false) -> TruncatedSrc
    | (false, true ) -> TruncatedRef
  in
  loop 0

let header basename max_abs_diff =
{html|<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<title>Diff for |html}^basename^{html|</title>
<link rel="icon" type="image/svg+xml" href="data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' height='100' width='100'%3E%3Cdefs%3E%3ClinearGradient id='grad1' x1='0%25' y1='0%25' x2='0%25' y2='100%25'%3E%3Cstop offset='0%25' style='stop-color:red'/%3E%3Cstop offset='50%25' style='stop-color:white'/%3E%3Cstop offset='100%25' style='stop-color:green'/%3E%3C/linearGradient%3E%3C/defs%3E%3Crect width='100' height='100' stroke='black' stroke-width='2' fill='url(%23grad1)'/%3E%3C/svg%3E%0A">
<style>
div.code div.filename {
  top: 0;
  position: sticky;
  z-index: 100;
  padding: 1lh;
  margin-bottom: 0;
  background-color: #F5F5F5;
  border: 2px solid #C0C0C0;
  font-family: monospace;
}

div.code pre {
  counter-reset: line;
  margin-top: 0;
  border: 2px solid #C0C0C0;
  border-top: 0px;
}

div.code pre span.line {
  display: inline-block;
  text-align: right;
  font-weight: bold;
  border-right: 2px solid #C0C0C0;
  padding: 0;
  margin-right: 0.5em;
  background-color: #F5F5F5;
  scroll-margin-top: 10lh;
}

div.code pre span.line:target {
  background-color: #CCCC00;
}

div.code pre span.line:hover {
  background-color: #FFFFCC;
}

div.code pre span.line a {
  display:inline-block;
  padding: 0 0.5em;
  width: 4ch;
  height:100%;
  color: #696969;
  text-decoration: none;
}

span.cmd {
  position: relative;
  --maxdelta: |html}^string_of_int max_abs_diff^{html|;
  --absdelta: max(var(--delta), -1 * var(--delta));
  --relativedelta: calc(var(--absdelta) / var(--maxdelta));
  --sign: calc(var(--delta) / var(--absdelta));
  background-color: hsl(max(var(--sign) * 1deg, -1 * var(--sign) * 120deg), 100%, calc(100% - (50% * var(--relativedelta))));
}

span.nosync {
  color: silver;
}

span.worsefg {
  color: red;
}

span.betterfg {
  color: green;
}

span.data {
  display: block;
  position: absolute;
  border: 2px solid black;
  border-radius: 10px;
  padding: 0.5lh;
  top: -2.5lh;
  left: 0;
  background-color: white;
  visibility: hidden;
  color: black;
}

span.cmd:hover {
  text-decoration: underline;
}

span.cmd:hover span.data {
  visibility: visible;
}
</style>
</head>
<body>
<div class="code">
|html}

let footer =
{html|</div>
</body>
</html>
|html}

type state = {
  data_ref       : Data.t;
  data_src       : Data.t;
  diff_status    : diff_status;
  mutable index  : int;
  mutable sbyte  : int;
  mutable ebyte  : int;
  mutable ic_src : int;
  mutable ic_ref : int option;
}

let initial_state : diff_status -> Data.t -> Data.t -> state =
    fun diff_status data_ref data_src ->
  let index = -1 in
  let (sbyte, ebyte, ic_src) = (0, 0, 0) in
  let ic_ref = Some(0) in
  {data_ref; data_src; diff_status; index; sbyte; ebyte; ic_src; ic_ref}

let next_cmd : state -> unit = fun s ->
  match s.index < Array.length s.data_src.Data.cs - 1 with
  | false -> s.sbyte <- max_int; s.ebyte <- max_int; ()
  | true  ->
  s.index <- s.index + 1;
  let d_src = s.data_src.Data.cs.(s.index) in
  let _ =
    match s.diff_status with
    | DifferAt(i) when i < d_src.Data.cmd_ebyte -> s.ic_ref <- None
    | _ -> ()
  in
  s.sbyte <- d_src.Data.cmd_sbyte;
  s.ebyte <- d_src.Data.cmd_ebyte;
  s.ic_src <- d_src.Data.cmd_ic;
  match (s.ic_ref, s.index < Array.length s.data_ref.Data.cs) with
  | (None, _    ) -> ()
  | (_   , false) -> s.ic_ref <- None
  | (_   , _    ) ->
  let d_ref = s.data_ref.Data.cs.(s.index) in
  if d_src.Data.cmd_sbyte <> d_ref.Data.cmd_sbyte then s.ic_ref <- None else
  if d_src.Data.cmd_ebyte <> d_ref.Data.cmd_ebyte then s.ic_ref <- None else
  s.ic_ref <- Some(d_ref.Data.cmd_ic)

let span_fg pct_diff fmt =
  if pct_diff > +0.01 then "<span class=\"worsefg\">"^^fmt^^"</span>" else
  if pct_diff < -0.01 then "<span class=\"betterfg\">"^^fmt^^"</span>" else
  fmt

let output_ref_with_offset oc (ref, diff) =
  let (sign, diff) = if diff < 0 then ("-", -diff) else ("+", diff) in
  let with_commas i =
    let s = Printf.sprintf "%#i" i in
    String.map (fun c -> if c = '_' then ',' else c) s
  in
  let ref = with_commas ref in
  let diff = with_commas diff in
  Printf.fprintf oc "%s%s%s" ref sign diff

let output_data ic_src ic_ref =
  let pp_data oc () =
    match ic_ref with
    | Some(ic_ref) ->
        let delta = ic_src - ic_ref in
        let pct = 100.0 *. (Float.of_int delta /. Float.of_int ic_ref) in
        Printf.fprintf oc "%a " output_ref_with_offset (ic_ref, delta);
        Printf.fprintf oc ("("^^span_fg pct "%+0.2f%%"^^")") pct;
    | None ->
        Printf.fprintf oc "%i (no reference)" ic_src
  in
  Printf.printf "<span class=\"data\">%a</span>" pp_data ()

let generate_pre : string -> diff_status -> Data.t -> Data.t -> unit =
    fun src diff data_ref data_src ->
  Printf.printf "<pre>\n";
  let state = initial_state diff data_ref data_src in
  next_cmd state;
  let in_cmd = ref false in
  let prev = ref '\n' in
  let line = ref 0 in
  let fn i c =
    if !prev = '\n' then begin
      let line = incr line; !line in
      Printf.printf "<span id=\"%i\" class=\"line\">" line;
      Printf.printf "<a href=\"#%i\">%i</a></span>" line line
    end;
    begin
      match !in_cmd with
      | true  when i < state.ebyte -> ()
      | true                       ->
          Printf.printf "</span>";
          in_cmd := false;
          next_cmd state
      | false when i < state.sbyte -> ()
      | false                      ->
          in_cmd := true;
          match state.ic_ref with
          | None        ->
              Printf.printf "<span class=\"cmd nosync\">";
              output_data state.ic_src state.ic_ref
          | Some ic_ref ->
              let delta = state.ic_src - ic_ref in
              Printf.printf "<span class=\"cmd\" style=\"--delta: %i\">" delta;
              output_data state.ic_src state.ic_ref
    end;
    prev := c;
    match c with
    | '<' -> output_string stdout "&lt;"
    | '>' -> output_string stdout "&gt;"
    | _ -> output_char stdout c
  in
  String.iteri fn src;
  Printf.printf "</pre>\n"

type global_data = {
  max_abs_diff : int; (* Non-negative. *)
}

let generate_code_header : string -> int -> int -> unit =
    fun file ic_ref ic_src ->
  Printf.printf "<div class=\"filename\">";
  Printf.printf "Performance difference for [%s]: " file;
  let delta = ic_src - ic_ref in
  let pct = 100.0 *. (Float.of_int delta /. Float.of_int ic_ref) in
  Printf.printf "%a " output_ref_with_offset (ic_ref, delta);
  Printf.printf ("("^^span_fg pct "%+0.2f%%"^^")") pct;
  Printf.printf "</div>\n"

let gather_global_data : diff_status -> Data.t -> Data.t -> global_data =
    fun diff data_ref data_src ->
  let diff = match diff with DifferAt(n) -> n | _ -> max_int in
  let rec process max_abs_diff data_ref data_src =
    match (data_ref, data_src) with
    | ([], _) | (_, []) -> max_abs_diff
    | (dr :: data_ref, ds :: data_src) ->
        if diff < ds.Data.cmd_ebyte then max_abs_diff else
        let ic_ref = dr.Data.cmd_ic in
        let ic_src = ds.Data.cmd_ic in
        let max_abs_diff = max max_abs_diff (abs (ic_src - ic_ref)) in
        process max_abs_diff data_ref data_src
  in
  let data_ref = Array.to_list data_ref.Data.cs in
  let data_src = Array.to_list data_src.Data.cs in
  let max_abs_diff = process 0 data_ref data_src in
  {max_abs_diff}

let _ =
  let ref = input_file src_ref in
  let src = input_file src_new in
  let diff = diff_status ref src in
  let data_ref = input_data data_ref in
  let data_src = input_data data_new in
  let {max_abs_diff} = gather_global_data diff data_ref data_src in
  output_string stdout (header (Filename.basename src_new) max_abs_diff);
  generate_code_header src_new data_ref.ic data_src.ic;
  generate_pre src diff data_ref data_src;
  output_string stdout footer;
  Printf.fprintf stdout "%!"
