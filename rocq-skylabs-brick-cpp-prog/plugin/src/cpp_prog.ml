(*
 * Copyright (c) 2025 BlueRock Security, Inc.
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

module Cpp2v = Rocq_skylabs_brick_plugin.Cpp2v
open Cpp2v

let temp_file ?(prefix="ocaml_temp_") ?(suffix=".tmp") content =
  let temp_file = Filename.temp_file prefix suffix in
  let oc = open_out temp_file in
  try
    output_string oc content;
    flush oc;
    close_out oc;
    let unlink () =
      try Sys.remove temp_file
      with _ -> ()
    in
    temp_file, unlink
  with e ->
    close_out_noerr oc;
    let _ = try Sys.remove temp_file with _ -> () in
    raise e

let flags_separator = Str.regexp "[ \n\r\x0c\t]+"

let separated_path_option =
  Str.regexp "^\\(-F\\|-I\\|-idirafter\\|-iframework\\|-iframeworkwithsysroot\\|-imacros\\|-include\\|-include-pch\\|-iquote\\|-isysroot\\|-isystem\\|-ivfsoverlay\\|-resource-dir\\|--sysroot\\)$"

let joined_path_option =
  Str.regexp "^\\(-F\\|-I\\|-idirafter\\|-iframeworkwithsysroot\\|-iframework\\|-iquote\\|-isysroot\\|-isystem\\)\\(.+\\)$"

let joined_sysroot_option =
  Str.regexp "^--sysroot=\\(.+\\)$"

let should_warn (flags : string) : bool =
  let is_relative_path path =
    path <> "" && Filename.is_relative path
  in
  let joined_path flag =
    if Str.string_match joined_path_option flag 0 then
      Some (Str.matched_group 2 flag)
    else if Str.string_match joined_sysroot_option flag 0 then
      Some (Str.matched_group 1 flag)
    else
      None
  in
  let rec go = function
    | [] -> false
    | flag :: path :: rest when Str.string_match separated_path_option flag 0 ->
      is_relative_path path || go rest
    | flag :: rest ->
      match joined_path flag with
      | Some path -> is_relative_path path || go rest
      | None -> go rest
  in
  go (Str.split flags_separator flags)

let%test "should_warn ignores flags without paths" =
  not (should_warn "-std=c++23 -Wall -DNAME=value")

let%test "should_warn ignores absolute separated path flags" =
  not (should_warn "-I /usr/include -isystem /opt/include --sysroot /opt/sysroot")

let%test "should_warn ignores absolute joined path flags" =
  not (should_warn "-I/usr/include -isystem/usr/include --sysroot=/opt/sysroot")

let%test "should_warn detects separated relative path flags" =
  should_warn "-I include" &&
  should_warn "-isystem ../include" &&
  should_warn "-include header.hpp" &&
  should_warn "--sysroot sysroot"

let%test "should_warn detects joined relative path flags" =
  should_warn "-Iinclude" &&
  should_warn "-isystem../include" &&
  should_warn "--sysroot=sysroot"

let cpp_prog_warn : ?loc:Loc.t -> Pp.t -> unit =
  let category = CWarnings.create_category ~name:"brick" () in
  CWarnings.create ~name:"cpp.prog" ~category ~default:CWarnings.Enabled Pp.(fun x -> x ++ fnl ())

let cpp_command_prog (attrs : attrs) name flags prog =
  let { check_duplicates; elaborate; check_types; with_templates } = attrs in
  let temp_cpp, unlink_cpp = temp_file ~suffix:".cpp" prog in
  let temp_v = Filename.temp_file "_" ".v" in
  let unlink_v () =
    try Sys.remove temp_v
    with _ -> ()
  in
  Fun.protect ~finally:(fun () -> unlink_cpp (); unlink_v ()) @@ fun () ->
  let flags =
    let flags =
      match flags with
      | None -> []
      | Some flags ->
        if should_warn flags then
          Feedback.msg_notice Pp.(str "Note that cpp.prog does not guarantee the working directory," ++ Pp.brk (0,0) ++
                                  str "so relative paths may yield inconsistent results between different editors." ++ fnl () ++
                                  str "Current working directory: " ++ str (Unix.getcwd ())) ;
        Str.split flags_separator flags
    in
    ["cpp2v";
     "-for-interactive"; Names.Id.to_string name;
     "--no-sharing"; (* to avoid polluting the namespace. It would be better to put this in a [Module]
                         if we are not in a [Section] *)
     "-o"; temp_v;
     temp_cpp] @
    (if with_templates then [] else ["--no-templates"]) @
    (if elaborate then ["--elaborate"] else ["--no-elaborate"]) @
    (if check_types then ["--check-types"] else []) @
    (match check_duplicates with
     | None -> []
     | Some Error -> ["-attributes";"duplicates(error)"]
     | Some Warn -> ["-attributes";"duplicates(warn)"]
     | Some Ignore -> ["-attributes";"duplicates(ignore)"]) @
    ("--" :: flags)
  in
  match Unix.open_process_args_full "cpp2v" (Array.of_list flags) (Unix.environment ()) with
  | exception Unix.Unix_error (err, _, _) ->
    CErrors.user_err Pp.(str "Running command `cpp2v` exited with error: " ++ str (Unix.error_message err))

  | streams ->
    let _stdin, _stdout, stderr = streams in

    let rec read_all channel buffer =
      try
        let line = input_line channel in
        Buffer.add_string buffer line;
        Buffer.add_char buffer '\n';
        read_all channel buffer
      with End_of_file -> buffer
    in

    let stderr_buffer = Buffer.create 4096 |> read_all stderr in
    let msg_text (warn_err : Pp.t) (cpp2v_stderr : string) =
      Pp.(
        str "Invoking cpp2v " ++ warn_err ++ fnl() ++
        str cpp2v_stderr ++ fnl() ++
        str "cpp2v command line:" ++ fnl() ++ str "  " ++ prlist_with_sep (fun () -> str " ") str flags)
    in
    let process_status = Unix.close_process_full streams in
    let success =
      match process_status with
      | WEXITED 0 -> true
      | _ -> false
    in
    let process_failure_str =
      match process_status with
      | WEXITED 0 -> ""
      | WEXITED n -> Printf.sprintf "exited with code %d" n
      | WSIGNALED n -> Printf.sprintf "killed by signal %d" n
      | WSTOPPED n -> Printf.sprintf "stopped by signal %d" n
    in
    if not success then
      if Buffer.length stderr_buffer = 0 then
        CErrors.user_err Pp.(msg_text Pp.(str process_failure_str ++ str " with no error message!") "")
      else
        CErrors.user_err Pp.(msg_text Pp.(str process_failure_str ++ str " with the following warnings/errors!") (Buffer.contents stderr_buffer))
    else if Buffer.length stderr_buffer > 0 then
      cpp_prog_warn Pp.(msg_text Pp.(str "produced the following warnings!") (Buffer.contents stderr_buffer));

    (* this might have problems with coq-lsp if the required file has its own requires *)
    let current_state = Vernacstate.freeze_full_state () in
    let _new_state =
      Vernacinterp.interp ~intern:Vernacinterp.fs_intern ~st:current_state
        (CAst.make Vernacexpr.{ control = [] ;
                                attrs = [] ;
                                expr = VernacSynterp (VernacLoad (false (* not verbose *),
                                                                  temp_v (* filename *)))  })
    in
    ()

(*
   If we need to avoid using <<Load>>, e.g. to support coq-lsp, then we can use
   this structure.

  see: toplevel/vernac.ml:105
  let source = Option.default (Loc.InFile {dirpath=None; file}) source in
  let in_pa = Procq.Parsable.make ~loc:Loc.(initial source)
      (Gramlib.Stream.of_channel stdout) in

  (* I can loop this until it says None *)
  Procq.Entry.parse (Pvernac.main_entry None) in_pa

  assert false
*)
