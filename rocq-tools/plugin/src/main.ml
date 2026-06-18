(*
 * Copyright (C) 2026 SkyLabs AI, Inc.
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

let error msg =
  CErrors.user_err (Pp.str msg)

let _ =
  if Array.mem "-profile" Sys.argv then
    error "The glob-data-collector plugin can't be used with \"-profile\"."

let vfile =
  let vfile = Sys.argv.(Array.length Sys.argv - 1) in
  if not (String.ends_with ~suffix:".v" vfile) then
    error "The glob-data-collector plugin expects the Rocq file as last arg.";
  vfile

let feedback_to_json : Feedback.feedback -> Yojson.Safe.t = fun f ->
  ignore f; `Null

let collect_feedback : unit -> string =
  let rev_feedback = ref [] in
  let _ = Feedback.add_feeder (fun f -> rev_feedback := f :: !rev_feedback) in
  let collect () =
    let json = `List(List.rev_map feedback_to_json !rev_feedback) in
    let file = Filename.remove_extension vfile ^ ".glob.feedback.json" in
    Out_channel.with_open_text file @@ fun oc ->
    Yojson.Safe.pretty_to_channel ~std:true oc json;
    file
  in
  collect

let collect_profile : unit -> string =
  if NewProfile.is_profiling () then
    error "The glob-data-collector plugin expects profiling to be disabled.";
  let file = Filename.remove_extension vfile ^ ".glob.perf.json" in
  let oc = Out_channel.open_text file in
  let ff = Format.formatter_of_out_channel oc in
  NewProfile.(init {output = ff; fname = file});
  let collect () =
    NewProfile.finish ();
    Format.pp_print_flush ff ();
    Out_channel.close_noerr oc;
    file
  in
  collect

let hack_glob () =
  let glob = Filename.remove_extension vfile ^ ".glob" in
  Globfs.append ~glob ~file:(collect_feedback ());
  Globfs.append ~glob ~file:(collect_profile ())

let _ =
  Stdlib.at_exit hack_glob
