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

let check_no_comp () =
  let _NO_COMP = "ROCQ_PERF_NO_COMPILATION" in
  match Sys.getenv_opt _NO_COMP with
  | None          -> ()
  | Some("false") -> ()
  | Some("true")  ->
      panic "Error: failed following %s." _NO_COMP
  | Some(_)       ->
      panic "Error: %s can only have value \"true\" or \"false\"." _NO_COMP

type files = {
  glob : string;
  perf : string;
  summary : string;
  log : string;
  stderr : string;
  stdout : string;
}

let rocq_bin =
  match Sys.getenv_opt "DUNE_SOURCEROOT" with
  | None       -> "rocq"
  | Some(root) -> Filename.concat root "_build/install/default/bin/rocq"

let rocq_command args = Filename.quote_command rocq_bin args

let default args = (rocq_command args, None)

let compile args =
  if List.mem "-profile" args then
    panic "Error: option \"-profile\" not supported (used internally).";
  let is_vfile arg = String.ends_with ~suffix:".v" arg in
  match List.filter is_vfile args with
  | []      -> default args
  | [vfile] ->
      check_no_comp ();
      let base = Filename.chop_extension vfile in
      let glob = base ^ ".glob" in
      let files =
        let perf = glob ^ ".perf.json" in
        let summary = glob ^ ".perf.csvline" in
        let log = glob ^ ".log.json" in
        let stdout = glob ^ ".stdout" in
        let stderr = glob ^ ".stderr" in
        {glob; perf; summary; log; stdout; stderr}
      in
      let env =
        "ROCQ_PROFILE_COMPONENTS=command" ::
        ("BR_LOG_FILE=" ^ Filename.quote files.log) ::
        []
      in
      let cmd =
        rocq_command ("compile" :: "-profile" :: files.perf :: args)
      in
      let cmd = String.concat " " (env @ [cmd]) in
      let cmd =
        Printf.sprintf
          "(((%s | tee %s) 3>&1 1>&2 2>&3) | tee %s) 3>&1 1>&2 2>&3"
          cmd (Filename.quote files.stdout) (Filename.quote files.stderr)
      in
      let cmd = "set -o pipefail; " ^ cmd in
      let cmd = "bash -c '" ^ cmd ^ "'" in
      (cmd, Some(files))
  | _       -> panic "Error: multiple \".v\" files given."

let (cmd, files) =
  let args = List.tl (Array.to_list Sys.argv) in
  match args with
  | "compile" :: args | "c" :: args -> compile args
  | _ -> default args

let embed_perf_and_summary glob perf_file summary_file =
  let json =
    let open Yojson in
    try
      let json_profile = Basic.from_file perf_file in
      Sys.remove perf_file; json_profile
    with
    | Json_error(s) -> panic "Error: bad profiling data, %s." s
  in
  let perf =
    try Profile.extract json with Profile.Error(s) ->
      panic "Error: cannot extract the profiling data, %s." s
  in
  let data =
    let open Yojson in
    try Basic.to_string ~std:true (Data.to_json perf) with Json_error(s) ->
      panic "Error: cannot turn the data into JSON, %s." s
  in
  (* Embed the perf data. *)
  let key = Globfs.Key.of_file ~glob ~file:perf_file in
  Globfs.append_data ~glob ~key ~data;
  (* Embed the summary. *)
  let data =
    let open Data in
    Printf.sprintf "%i,%i,%i,%i\n" perf.ic perf.tm perf.mj perf.mn
  in
  let key = Globfs.Key.of_file ~glob ~file:summary_file in
  Globfs.append_data ~glob ~key ~data

let embed_log glob log_file =
  Globfs.append ~glob ~file:log_file;
  Sys.remove log_file

let non_empty_file file =
  let ic = In_channel.open_text file in
  let non_empty = In_channel.input_char ic <> None in
  In_channel.close_noerr ic; non_empty

let embed_stdout_and_stderr glob stdout_file stderr_file =
  if non_empty_file stdout_file then Globfs.append ~glob ~file:stdout_file;
  Sys.remove stdout_file;
  if non_empty_file stderr_file then Globfs.append ~glob ~file:stderr_file;
  Sys.remove stderr_file

let hack_glob {glob; perf; summary; log; stdout; stderr} =
  (* Extract and embed the performance data. *)
  embed_perf_and_summary glob perf summary;
  (* Embed the log if it was generated. *)
  if Sys.file_exists log && not (Sys.is_directory log) then
    embed_log glob log;
  (* Embed stdout and stderr. *)
  embed_stdout_and_stderr glob stdout stderr

let hack_glob files =
  try hack_glob files with
  | Profile.NoInstr -> () (* No instruction counts, do nothing. *)
  | Sys_error(msg)  -> panic "Error: %s." msg

let cleanup files =
  let rm file = try Sys.remove file with Sys_error(_) -> () in
  List.iter rm [files.log; files.perf; files.stdout; files.stderr]

let _ =
  let s = Sys.command cmd in
  Option.iter (if s = 0 then hack_glob else cleanup) files;
  exit s
