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


open Rocq_tools.Extra
open Rocq_tools.Code_quality

let dummy_pos : pos = {line = 0; c0 = -1; c1 = -1}

let main () =
  let lines, warnings, errors =
    let lines = In_channel.input_lines stdin in
    parse_lines (List.map parse_line lines)
  in
  let warn_line (i, line) =
    Printf.eprintf "Warning: dangling input line.\n% 5i | %s\n%!" i line
  in
  List.iter warn_line lines;
  let to_json file pos text (kind : [`Error|`Warning of string])  =
    let name =
      match kind with
      | `Error -> "error"
      | `Warning name -> "warning:" ^ name
    in
    let fingerprint =
      let data =
        let pos = match pos with Some(pos) -> pos | None -> dummy_pos in
        Printf.sprintf "%s,%i,%i,%i,%s,%s"
          file pos.line pos.c0 pos.c1 name text
      in
      Digest.to_hex (Digest.string data)
    in
    let pos =
      let pos = match pos with Some(pos) -> pos | None -> dummy_pos in
      let line = ("line", `Int(pos.line)) in
      let b = `Assoc([line; ("column", `Int(pos.c0))]) in 
      let e = `Assoc([line; ("column", `Int(pos.c1))]) in 
      `Assoc([("begin", b); ("end", e)])
    in
    let location = [("path", `String(file)); ("positions", pos)] in
    let severity =
      match kind with
      | `Error -> "critical"
      | `Warning _ -> "minor"
    in
    let fields =
      ("description", `String(text)       ) ::
      ("check_name" , `String(name)       ) ::
      ("fingerprint", `String(fingerprint)) ::
      ("severity"   , `String(severity)   ) ::
      ("location"   , `Assoc(location)    ) :: []
    in
    `Assoc(fields)
  in
  let error_to_json (e : Error.t) =  to_json e.file e.pos e.text (`Error) in
  let warning_to_json (w : Warning.t) = to_json w.file w.pos w.text (`Warning(w.name)) in
  let json = `List(List.map error_to_json errors @ List.map warning_to_json warnings) in
  Printf.printf "%a\n%!" (Yojson.Basic.pretty_to_channel ~std:true) json

let _ =
  try main () with
  | Sys_error(msg) -> panic "System error: %s" msg
