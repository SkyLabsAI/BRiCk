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

open Rocq_tools.Extra

let (csv, html) =
  match Sys.argv with
  | [|_; csv; html|] -> (csv, html)
  | _ -> panic "Usage: %s index.csv index.html" Sys.argv.(0)

type data_category =
  | Items of string * string list
  | Count of string * int 
  | Links of string * (string * string) list

let meaningful : data_category -> bool = fun c ->
  match c with
  | Items(_,l) -> l <> []
  | Count(_,n) -> n > 0
  | Links(_,l) -> l <> []

let data : data_category list =
  let nodata = ref [] in
  let nomoredata = ref [] in
  let newdata = ref [] in
  let identical = ref [] in
  let differror = ref [] in
  let refnotcompiled = ref [] in
  let srcnotcompiled = ref [] in
  let notcompiled = ref [] in
  let diff = ref [] in
  let added = ref [] in
  let removed = ref [] in
  let _ =
    try
      In_channel.with_open_text csv @@ fun ic ->
      try while true do
        let line = input_line ic in
        match String.split_on_char ',' line with
        (* No diff page. *)
        | [f; "nodata"        ] -> nodata         := f :: !nodata
        | [f; "nomoredata"    ] -> nomoredata     := f :: !nomoredata
        | [f; "newdata"       ] -> newdata        := f :: !newdata
        | [f; "identical"     ] -> identical      := f :: !identical
        | [f; "differror"     ] -> differror      := f :: !differror
        | [f; "refnotcompiled"] -> refnotcompiled := f :: !refnotcompiled
        | [f; "srcnotcompiled"] -> srcnotcompiled := f :: !srcnotcompiled
        | [f; "notcompiled"   ] -> notcompiled    := f :: !notcompiled
        | [f; "added"         ] -> added          := f :: !added
        | [f; "removed"       ] -> removed        := f :: !removed
        (* Diff page available. *)
        | [f; "diff"; d] -> diff := (f, d) :: !diff
        | [] -> ()
        | _ -> Printf.printf "Warning: cannot parse line %S.\n%!" line
      done with End_of_file -> ()
    with Sys_error(msg) -> panic "Error: %s" msg
  in
  let notcompiled = List.length !notcompiled in
  let refnotcompiled = List.sort String.compare !refnotcompiled in
  let srcnotcompiled = List.sort String.compare !srcnotcompiled in
  let nodata = List.length !nodata in
  let nomoredata = List.sort String.compare !nomoredata in
  let newdata = List.sort String.compare !newdata in
  let identical = List.sort String.compare !identical in
  let added = List.sort String.compare !added in
  let removed = List.sort String.compare !removed in
  let differror = List.sort String.compare !differror in
  let diff = List.sort (fun (s1,_) (s2,_) -> String.compare s1 s2) !diff in
  List.filter meaningful [
    Items("Errors while producing the HTML diff", differror);
    Links("Files with detailed diff", diff);
    Items("Files added", added);
    Items("Files removed", removed);
    Items("Data only in the reference", nomoredata);
    Items("Data only in the source", newdata);
    Count("Not compiled on either side", notcompiled);
    Items("Not compiled in the reference", refnotcompiled);
    Items("Not compiled in the source", srcnotcompiled);
    Count("Compiled with no data on either side", nodata);
    Items("Identical file and performance", identical);
  ]

let header =
{html|<!DOCTYPE html>
<html>
<head>
<title>Performance report</title>
<style>
</style>
</head>
<body>
|html}

let footer =
{html|</body>
</html>
|html}

let write_index : Out_channel.t -> data_category list -> unit = fun oc cs ->
  let out fmt = Printf.fprintf oc fmt in
  let out_category c =
    match c with
    | Items(title,l) ->
        out "  <h2>%s</h1>\n" title;
        out "  <ul>\n";
        List.iter (out "    <li>%s</li>\n") l;
        out "  </ul>\n"
    | Count(title,n) ->
        out "  <h2>%s: %i</h1>\n" title n
    | Links(title,l) ->
        out "  <h2>%s</h1>\n" title;
        out "  <ul>\n";
        List.iter (fun (f, l) ->
          out "    <li><a href=\"%s\">%s</a></li>\n" l f
        ) l;
        out "  </ul>\n"
  in
  out "%s" header;
  out "  <h1>Performance report</h1>\n";
  List.iter out_category cs;
  out "%s" footer

let _ =
  let fn oc = write_index oc data in
  try Out_channel.with_open_text html fn with
  | Sys_error(msg) -> panic "Error: %s" msg
