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

(** Short name for a standard formatter. *)
type 'a outfmt = ('a, Format.formatter, unit) format

module W = struct
  include Warning
  let pp : Format.formatter -> t -> unit =
    fun fmt {full; _} ->
    Format.fprintf fmt "%s\n" full
end
module E = struct
  include Error
  let pp : Format.formatter -> t -> unit =
    fun fmt {full; _} ->
    Format.fprintf fmt "%s\n" full
end

module type Set = sig
  include Set.S
  val pp : (Format.formatter -> elt -> unit) -> Format.formatter -> t -> unit
  val pp_elt : Format.formatter -> elt -> unit
end

module WS : Set with type elt = Warning.t = struct
  include Set.Make(W)
  let pp_elt = W.pp
  let pp pp_w fmt ws =
    iter (fun w -> Format.fprintf fmt "%a" pp_w w) ws
end
module ES : Set with type elt = Error.t = struct
  include Set.Make(E)
  let pp_elt = E.pp
  let pp pp_w fmt ws =
    iter (fun w -> Format.fprintf fmt "%a" pp_w w) ws
end

module Analysis = struct
  type 's data = {
    before      : 's;
    after       : 's;
    appeared    : 's;
    disappeared : 's;
  }
  type t = {
    warnings : WS.t data;
    errors   : ES.t data;
  }
end

module Markdown = struct
  let output fmt (a : Analysis.t) =
    let open Analysis in
    let {warnings={appeared=w_appeared; disappeared=w_disappeared; _} as ws;
         errors  ={appeared=e_appeared; disappeared=e_disappeared;_} as es} = a in

    let table fmt =
      Format.fprintf fmt "\
        |        |Before|New |Fixed|After|\n\
        |--------|-----:|---:|----:|----:|\n\
        |Errors  | %i   | %i | %i  | %i  |\n\
        |Warnings| %i   | %i | %i  | %i  |\n\n"
        (ES.cardinal es.before) (ES.cardinal es.appeared) (ES.cardinal es.disappeared) (ES.cardinal es.after)
        (WS.cardinal ws.before) (WS.cardinal ws.appeared) (WS.cardinal ws.disappeared) (WS.cardinal ws.after);
    in

    let in_summary : ?is_open:bool -> _ -> header:_ -> _ = fun ?(is_open=false) fmt ~header body ->
      Format.fprintf fmt "<details%s><summary>\n\n" (if is_open then " open" else "");
      header fmt;
      Format.fprintf fmt "\n</summary>\n";
      body fmt;
      Format.fprintf fmt "</details>\n\n";
    in

    if WS.is_empty w_appeared &&
       WS.is_empty w_disappeared &&
       ES.is_empty e_appeared &&
       ES.is_empty e_disappeared
    then begin
      Format.fprintf fmt "# No Changes in Warnings or Errors\n%!";
      table fmt;
    end
    else begin
      Format.fprintf fmt "# Changes in Warnings or Errors\n%!";
      table fmt;
      let header fmt symbol title num =
        Format.fprintf fmt "## %s %s (%i)\n" symbol title num;
      in
      let code_block pp_content fmt content =
        Format.fprintf fmt "```\n%a```\n" pp_content content
      in
      if not @@ ES.is_empty e_disappeared then begin
        let header fmt = header fmt ":negative_squared_cross_mark:" "Fixed Errors" (ES.cardinal e_disappeared) in
        in_summary fmt ~header @@ fun fmt ->
        Format.fprintf fmt "\n%a\n" (ES.pp @@ code_block ES.pp_elt) e_disappeared;
      end;
      if not @@ WS.is_empty w_disappeared then begin
        let header fmt = header fmt ":green_heart:" "Fixed Warnings" (WS.cardinal w_disappeared) in
        in_summary fmt ~header @@ fun fmt ->
        Format.fprintf fmt "\n%a\n" (WS.pp @@ code_block WS.pp_elt) w_disappeared;
      end;
      if not @@ ES.is_empty e_appeared then begin
        let header fmt = header fmt ":x:" "New Errors" (ES.cardinal e_appeared) in
        in_summary fmt ~is_open:true ~header @@ fun fmt ->
        Format.fprintf fmt "\n%a\n" (ES.pp @@ code_block ES.pp_elt) e_appeared;
      end;

      if not @@ WS.is_empty w_appeared then begin
        let header fmt = header fmt ":warning:" "New Warnings" (WS.cardinal w_appeared) in
        in_summary fmt ~is_open:true ~header @@ fun fmt ->
        Format.fprintf fmt "\n%a\n" (WS.pp @@ code_block WS.pp_elt) w_appeared;
      end;
    end
end

type glob_out = {
  src_file : string;
  std_out : string list;
  std_err : string list;
}

let ensure_file file =
  if try Sys.is_directory file with Sys_error(_) -> false then
    panic "File expected, [%s] is a directory." file;
  if not (Sys.file_exists file) then
    panic "No such file or directory [%s]." file

let to_glob_out : strip_prefix:string -> string -> glob_out option =
  let re = Str.regexp {|\.glob\.\(stdout\|stderr\)$|} in
  fun ~strip_prefix filename ->
  let is_std_out = String.ends_with ~suffix:".glob.stdout" filename in
  let is_std_err = String.ends_with ~suffix:".glob.stderr" filename in
  if not (is_std_out || is_std_err) then begin
    Printf.eprintf "%s is neither a .glob.stdout nor a .glob.stderr file" filename;
    None
  end
  else begin
    let src_file = Str.replace_first re ".v" filename in
    let src_file = if String.starts_with ~prefix:strip_prefix src_file then
        let n = String.length strip_prefix in
        String.sub src_file n (String.length src_file - n)
      else
        src_file
    in
    let std_out =
      if is_std_out then begin
        ensure_file filename;
        get_lines (open_in filename) (fun x -> x)
      end
      else
        []
    in
    let std_err =
      if is_std_err then begin
        ensure_file filename;
        get_lines (open_in filename) (fun x -> x)
      end
      else
        []
    in
    Some { src_file; std_out; std_err }
  end

type dune_type =
  | Rocq
  | Cram
  | Diff

type dune_out = {
  src_file : string;
  file_type : dune_type;
  output : string list;      (* dune does not dinstinguish stderr and stdout. *)
}

let to_dune_out : fname:string -> dune_out list =
  let re_rocq = Str.regexp {|\bcoqc.* \([^ ]+\.v\))$|} in
  let re_cram = Str.regexp {|\bpatdiff.* \([^ ]+\)\.corrected'|} in
  let re_diff = Str.regexp {|\bpatdiff.* \([^ ]+\) [^ ]+\'|} in
  fun ~fname ->
  let open Yojson.Basic in
  let json = from_file ~fname fname in
  let list = Util.to_list json in
  let list = List.map Util.to_assoc list in
  let list =
    let f a =
      (Util.to_string @@ List.assoc "command" a,
      List.map Util.to_string @@ Util.to_list @@ List.assoc "output" a)
    in
    List.map f list in
  let list =
    let f (cmd, out) =
      let file_type =
        try
          let _ = Str.search_forward re_rocq cmd 0 in
          Some Rocq
        with Not_found ->
        try
          let _ = Str.search_forward re_cram cmd 0 in
          Some Cram
        with Not_found ->
        try
          let _ = Str.search_forward re_diff cmd 0 in
          Some Diff
        with Not_found -> None
      in
      Option.bind file_type @@ fun file_type ->
        let src_file = Str.matched_group 1 cmd in
        let output = List.filter (fun x -> x <> "") out in
        Some { src_file; file_type; output }
    in
    List.filter_map f list
  in
  list

let analyse fmt ~before_dune ~after_dune ~before_globs ~after_globs =

  let nonempty_stdout_warning src_file output =
    let text = Format.sprintf "File \"%s\", line 0, characters 0-0:\nWarning: Non-empty stdout when building using coqc:\n%s\n[non-empty-stdout,dummy]" src_file output in
    W.{ file = src_file; pos = None; name = "non-empty-stdout,dummy"; text; full = text }
  in
  let dangling_output_warning src_file output =
    let text = Format.sprintf "File \"%s\", line 0, characters 0-0:\nWarning: Dangling output when building using coqc:\n%s\n[dangling-output-stdout,dummy]" src_file output in
    W.{ file = src_file; pos = None; name = "dangling-output,dummy"; text; full = text }
  in

  let parse globs dunes =
    let glob (ws, es) {src_file; std_err; std_out} =
      let (dangling_lines, w,e) = parse_lines (List.map parse_line std_err) in
      let dangling = List.map (fun (_, txt) -> dangling_output_warning src_file txt) dangling_lines in
      let w =
        if std_out = [] then w else begin
          nonempty_stdout_warning src_file (String.concat "\n" std_out) :: w
        end
      in
      (List.rev_append w @@ List.rev_append dangling ws, List.rev_append e es)
    in

    let dune (ws, es) {src_file; file_type; output} =
      match file_type with
      | Rocq ->
        let (dangling_lines, w, e) = parse_lines (List.map parse_line output) in
        let dangling = List.map (fun (_, txt) -> dangling_output_warning src_file txt) dangling_lines in
        (List.rev_append w @@ List.rev_append dangling ws, List.rev_append e es)
      | Cram | Diff ->
        (* The first two lines are just diff output *)
        let output = List.tl @@ List.tl @@ output in
        let (dangling_lines, w, e) = parse_lines ~assume_errors:true (List.map parse_line output) in
        let dangling = List.map (fun (_, txt) -> dangling_output_warning src_file txt) dangling_lines in
        (List.rev_append w @@ List.rev_append dangling ws, List.rev_append e es)
    in

    List.fold_left glob ([], []) globs |> fun res ->
    List.fold_left dune res dunes
  in

  let (warnings1, errors1) = parse before_globs before_dune in
  let (warnings2, errors2) = parse after_globs after_dune in

  (* Format.efprintf fmt "size of warnings1 = %i\n" (List.length warnings1);  *)
  (* Format.efprintf fmt "size of warnings2 = %i\n" (List.length warnings2);  *)
  (* Format.efprintf fmt "size of errors1 = %i\n" (List.length errors1);  *)
  (* Format.efprintf fmt "size of errors2 = %i\n" (List.length errors2);  *)

  let warnings =
    let before = WS.of_list warnings1 in
    let after = WS.of_list warnings2 in
    let appeared = WS.diff after before in
    let disappeared = WS.diff before after in
    Analysis.{ before; after; appeared; disappeared }
  in

  let errors =
    let before = ES.of_list errors1 in
    let after = ES.of_list errors2 in
    let appeared = ES.diff after before in
    let disappeared = ES.diff before after in
    Analysis.{ before; after; appeared; disappeared }
  in

  Markdown.output fmt {errors; warnings}


let einfo : 'a outfmt -> 'a = fun fmt ->
  Format.eprintf (fmt ^^ "%!")

module Args = struct
  type t = {
    before_globs: glob_out list;
    before_dune : dune_out list;
    after_globs : glob_out list;
    after_dune : dune_out list;
  }
  let empty = {
    before_globs = [];
    after_globs = [];
    before_dune = [];
    after_dune = [];
  }
end
open Args

let usage : ?error:bool -> string -> 'a = fun ?(error=false) prog_name ->
  if error then panic "Usage: %s [--before-globs-from-file file-with-glob-files ..] [--after-globs-from-file file-with-glob-files ..] [--before-dune dune-log.json ..] [--after-dune dune-log.json ..]" prog_name;
  einfo "Usage: %s [--before-globs-from-file file-with-glob-files ..] [--after-globs-from-file file-with-glob-files ..] [--before-dune dune-log.json ..] [--after-dune dune-log.json ..]" prog_name;
  exit 0

let main () =
  let (prog_name, args) =
    let args = List.tl (Array.to_list Sys.argv) in
    (Sys.argv.(0), args)
  in
  let rec parse_args state args =
    let is_flag arg = String.length arg > 0 && arg.[0] = '-' in
    match args with
    | ("--help" | "-h")             :: _                     ->
        usage prog_name
    | "--before-globs-from-file" :: file  :: args            ->
        ensure_file file;
        let strip_prefix = Filename.dirname file ^ "/" in
        let new_before_globs = List.filter_map (fun x -> x) @@ get_lines (open_in file) (to_glob_out ~strip_prefix) in
        let before_globs = List.rev_append new_before_globs state.before_globs in
        parse_args {state with before_globs} args
    | "--after-globs-from-file" :: file   :: args            ->
        ensure_file file;
        let strip_prefix = Filename.dirname file ^ "/" in
        let new_after_globs = List.filter_map (fun x -> x) @@ get_lines (open_in file) (to_glob_out ~strip_prefix) in
        let after_globs = List.rev_append new_after_globs state.after_globs in
        parse_args {state with after_globs} args
    | "--before-dune" :: file       :: args                  ->
        ensure_file file;
        let new_before_dune = to_dune_out ~fname:file in
        let before_dune = List.rev_append new_before_dune state.before_dune in
        parse_args {state with before_dune} args
    | "--after-dune" :: file       :: args                  ->
        ensure_file file;
        let new_after_dune = to_dune_out ~fname:file in
        let after_dune = List.rev_append new_after_dune state.after_dune in
        parse_args {state with after_dune} args
    | arg                           :: _ when is_flag arg    ->
        panic "Invalid command line argument \"%s\"." arg;
    | _ :: _ ->
        usage ~error:true prog_name
    | []                                                     ->
        state

  in
  let {before_dune; after_dune; before_globs; after_globs} = parse_args empty args in
  analyse (Format.formatter_of_out_channel stdout) ~before_dune ~after_dune ~before_globs ~after_globs

let _ =
  try main () with
  | Sys_error(msg) -> panic "System error: %s" msg
