(*
 * Copyright (c) 2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(* Disable exception backtraces, overriding effects of the Base library.
   Backtraces affect all Rocq user errors, not just anomalies. *)
let _ =
  let _ = Base.compare_option in
  Printexc.record_backtrace false

type report_level =
  | Ignore
  | Warn
  | Error

type attrs = {
  check_duplicates : report_level option;
  elaborate : bool;
  check_types : bool;
  with_templates : bool;
}

let attributes =
  let open Attributes in
  let open Attributes.Notations in
  let name = "duplicates" in
  let duplicates =
    qualify_attribute "duplicates" @@ attribute_of_list [
      ("warn", single_key_parser ~name ~key:"warn" Warn);
      ("error", single_key_parser ~name ~key:"error" Error);
      ("ignore", single_key_parser ~name ~key:"ignore" Ignore);
    ]
  in
  let bool_attr name = map (fun v -> v = Some true) (bool_attribute ~name) in
  let make ((args, with_templates), no_templates) =
    let ((check_duplicates, elaborate), check_types) = args in
    let with_templates = with_templates || not no_templates in
    {check_duplicates; elaborate; check_types; with_templates}
  in
  let attrs =
    duplicates ++
    bool_attr "elaborate" ++
    bool_attr "check_types" ++
    bool_attr "with_templates" ++
    bool_attr "no_templates"
  in
  map make attrs

let prog_attributes =
  let open Attributes.Notations in
  attributes ++ Attributes.payload_attribute ?cat:None ~name:"environment"

let lib_ref t =
  Rocqlib.lib_ref ("skylabs.lang.cpp.parser.translation_unit." ^ t)

let (cpp2v_category, cpp2v_warning) =
  CWarnings.create_hybrid ~name:"cpp2v" ()

let duplicate_symbols =
  CWarnings.create_msg cpp2v_warning ()

let duplicate_symbols_printer (env, evd, err) =
  let open Pp in
  str "Duplicate symbols found!" ++ fnl () ++
  Printer.pr_econstr_env env evd err ++ str "."

let _ =
  CWarnings.register_printer duplicate_symbols duplicate_symbols_printer

let to_econstr t =
  match t with
  | Names.GlobRef.ConstRef c ->
    EConstr.mkConstU (c, EConstr.EInstance.empty)
  | Names.GlobRef.IndRef ind ->
    EConstr.mkIndU (ind, EConstr.EInstance.empty)
  | _ ->
    Feedback.msg_debug (Names.GlobRef.print t) ;
    assert false

let decl_of_ref t =
  match lib_ref t with
  | Names.GlobRef.ConstRef c ->
    let decl = Global.lookup_constant c in
    decl
  | _ -> assert false

let force_body (t : _ Declarations.pconstant_body) =
  match t.const_body with
  | Declarations.Def d -> d
  | _ -> assert false

let report_duplicates check_duplicates env evd err =
  match EConstr.kind evd err with
  | Constr.App (hd, [| _ |]) when EConstr.isConstruct evd hd ->
    ()
  | _ ->
    begin
    match check_duplicates with
    | Some Error ->
      CErrors.user_err @@ duplicate_symbols_printer (env, evd, err)
    | Some Warn -> CWarnings.warn duplicate_symbols (env, evd, err)
    | Some Ignore | None -> ()
    end

let cpp_command (attrs : attrs) name (abi : Constrexpr.constr_expr option)
    (defns : Constrexpr.constr_expr list) =
  (* Create the definition *)
  let {check_duplicates; _} = attrs in
  let env = Global.env() in
  let e_decl = to_econstr (lib_ref "t") in
  let e_decl_skip = to_econstr (lib_ref "skip") in
  let inst =
    let t = Constr.kind (decl_of_ref "empty_array").const_type in
    let h = match t with Constr.App(h, _) -> h | _ -> assert false in
    match Constr.kind h with Constr.Const(_,inst) -> inst | _ -> assert false
  in
  let evd = Evd.from_env env in
  let (abi, evd) =
    match abi with
    | None -> (to_econstr (lib_ref "abi_default"), evd)
    | Some abi ->
    let expected_type = Pretyping.OfType (to_econstr (lib_ref "abi_type")) in
    let (abi, ustate) =
      Constrintern.interp_constr ~expected_type env evd abi
    in
    (abi, Evd.from_ctx ustate)
  in
  let (body, evd) =
    let expected_type = Pretyping.OfType e_decl in
    let f (acc, evd) defn =
      (* TODO: the docs say that i should not use this function,
         but it doesn't seem like i can give an expected type to
         [Constrintern.interp_constr_evars] *)
      let (body, ustate) =
        Constrintern.interp_constr ~expected_type env evd defn
      in
      (body :: acc, Evd.from_ctx ustate)
    in
    List.fold_left f ([], evd) defns
  in
  let body =
    let inst = EConstr.EInstance.make inst in
    EConstr.mkArray (inst, Array.of_list (List.rev body), e_decl_skip, e_decl)
  in
  let body = EConstr.mkApp (to_econstr (lib_ref "decls"), [|body; abi|]) in
  let body =
    let rt = force_body (decl_of_ref "result_type") in
    Vnorm.cbv_vm env evd body (EConstr.of_constr rt)
  in
  (* The term should have type <<translation_unit.t * dup_info>>
     where <<dup_info>> is a list.
   *)
  match EConstr.kind evd body with
  | Constr.App (hd, [|_ ;_ ;body; err|]) when EConstr.isConstruct evd hd ->
      report_duplicates check_duplicates env evd err;
      let cinfo = Declare.CInfo.make ~name ~typ:None () in
      let info = Declare.Info.make () in
      ignore (Declare.declare_definition ~info ~cinfo ~opaque:false ~body evd)
  | _ ->
      CErrors.user_err Pp.(str "cpp.prog failed to return a head \
        constructor. Please report!" ++ fnl () ++
        Printer.pr_econstr_env env evd body)

let flags_separator = Str.regexp "[ \n\r\x0c\t]+"

let option_regexp options suffix =
  let alternatives = String.concat "\\|" (List.map Str.quote options) in
  Str.regexp ("^\\(" ^ alternatives ^ "\\)" ^ suffix ^ "$")

let separated_path_option =
  option_regexp [
    "-F";
    "-I";
    "-idirafter";
    "-iframework";
    "-iframeworkwithsysroot";
    "-imacros";
    "-include";
    "-include-pch";
    "-iquote";
    "-isysroot";
    "-isystem";
    "-ivfsoverlay";
    "-resource-dir";
    "--sysroot";
  ] ""

let joined_path_option =
  option_regexp [
    "-F";
    "-I";
    "-idirafter";
    "-iframeworkwithsysroot";
    "-iframework";
    "-iquote";
    "-isysroot";
    "-isystem";
  ] "\\(.+\\)"

let joined_sysroot_option =
  Str.regexp "^--sysroot=\\(.+\\)$"

let has_relative_path_flag (flags : string) : bool =
  let is_relative_path path = path <> "" && Filename.is_relative path in
  let joined_path flag =
    if Str.string_match joined_path_option flag 0 then
      Some (Str.matched_group 2 flag)
    else if Str.string_match joined_sysroot_option flag 0 then
      Some (Str.matched_group 1 flag)
    else
      None
  in
  let rec go flags =
    match flags with
    | [] -> false
    | flag :: path :: rest
      when Str.string_match separated_path_option flag 0 ->
        is_relative_path path || go rest
    | flag :: rest ->
        match joined_path flag with
        | Some path -> is_relative_path path || go rest
        | None -> go rest
  in
  go (Str.split flags_separator flags)

let%test "flags without paths are ignored" =
  not (has_relative_path_flag "-std=c++23 -Wall -DNAME=value")

let%test "absolute separated path flags are ignored" =
  not (has_relative_path_flag
      "-I /usr/include -isystem /opt/include --sysroot /opt/sysroot")

let%test "absolute joined path flags are ignored" =
  not (has_relative_path_flag
      "-I/usr/include -isystem/usr/include --sysroot=/opt/sysroot")

let%test "relative separated path flags are detected" =
  has_relative_path_flag "-I include" &&
  has_relative_path_flag "-isystem ../include" &&
  has_relative_path_flag "-include header.hpp" &&
  has_relative_path_flag "--sysroot sysroot"

let%test "relative joined path flags are detected" =
  has_relative_path_flag "-Iinclude" &&
  has_relative_path_flag "-isystem../include" &&
  has_relative_path_flag "--sysroot=sysroot"

let cpp_prog_warn : ?loc:Loc.t -> Pp.t -> unit =
  let name = "cpp.prog" in
  let category = CWarnings.create_category ~name:"brick" () in
  let default = CWarnings.Enabled in
  CWarnings.create ~name ~category ~default Pp.(fun x -> x ++ fnl ())

let generated_filenames (loc : Loc.t) =
  match loc.Loc.fname with
  | Loc.ToplevelInput ->
      let prefix = "cpp.prog_" in
      Filename.(temp_file prefix ".cpp", temp_file prefix ".v")
  | Loc.InFile({file; _ }) ->
      let col = loc.Loc.bp - loc.Loc.bol_pos in
      let stem = Printf.sprintf "%s.%d_%d" file loc.Loc.line_nb col in
      (stem ^ ".cpp", stem ^ ".v")

let warn_about_relative_paths flags =
  match has_relative_path_flag flags with false -> () | true ->
  let msg =
    let open Pp in
    str "Note that cpp.prog does not guarantee the working directory," ++
    brk (0,0) ++
    str "so relative paths may yield inconsistent results between " ++
    str "different editors." ++ fnl () ++
    str "Current working directory: " ++ str (Unix.getcwd ())
  in
  Feedback.msg_notice msg

let parse_flags flags =
  match flags with
  | None -> []
  | Some flags ->
    warn_about_relative_paths flags;
    Str.split flags_separator flags

let duplicate_arguments check_duplicates =
  match check_duplicates with
  | None -> []
  | Some Error -> ["-attributes"; "duplicates(error)"]
  | Some Warn -> ["-attributes"; "duplicates(warn)"]
  | Some Ignore -> ["-attributes"; "duplicates(ignore)"]

let cpp2v_arguments (attrs : attrs) name cpp_file v_file flags =
  let {check_duplicates; elaborate; check_types; with_templates} = attrs in
  let name = Names.Id.to_string name in
  let argv =
    ["cpp2v"; "-for-interactive"; name; "--no-sharing"] @
    ["-o"; v_file; cpp_file] @
    (if with_templates then [] else ["--no-templates"]) @
    (if elaborate then ["--elaborate"] else ["--no-elaborate"]) @
    (if check_types then ["--check-types"] else []) @
    duplicate_arguments check_duplicates @
    ("--" :: parse_flags flags)
  in
  Array.of_list argv

let write_cpp file prog =
  Out_channel.with_open_text file @@ fun oc ->
  Out_channel.output_string oc prog

let cpp2v_message flags outcome stderr =
  let open Pp in
  str "Invoking cpp2v " ++ outcome ++ fnl () ++ str stderr ++ fnl () ++
  str "cpp2v command line:" ++ fnl () ++
  str "  " ++ prvecti_with_sep (fun () -> str " ") (fun _ -> str) flags

let process_failure (status : Unix.process_status) =
  match status with
  | WEXITED n -> Printf.sprintf "exited with code %d" n
  | WSIGNALED n -> Printf.sprintf "killed by signal %d" n
  | WSTOPPED n -> Printf.sprintf "stopped by signal %d" n

let report_cpp2v_result flags stderr (status : Unix.process_status) =
  match status with
  | WEXITED 0 when stderr = "" -> ()
  | WEXITED 0 ->
      let msg = Pp.str "produced the following warnings!" in
      cpp_prog_warn (cpp2v_message flags msg stderr)
  | status ->
      let failure = process_failure status in
      let outcome =
        match stderr with
        | "" -> Pp.(str failure ++ str " with no error message!")
        | _  -> Pp.(str failure ++ str " with the following warnings/errors!")
      in
      CErrors.user_err (cpp2v_message flags outcome stderr)

let absolute_path path =
  if Filename.is_relative path then Filename.concat (Sys.getcwd ()) path else path

let configured_arguments command config flags =
  Array.append [|command; config|] (Array.sub flags 1 (Array.length flags - 1))

let%test "configured arguments preserve paths, flags and empty arguments" =
  let command = "/tools with spaces/cpp2v_inline" in
  let config = "/project with spaces/cpp_environment" in
  let flags = [|"cpp2v"; "input with spaces.cpp"; "-DVALUE=literal $value"; ""|] in
  configured_arguments command config flags =
    [|command; config; "input with spaces.cpp"; "-DVALUE=literal $value"; ""|]

let cpp2v_invocation environment flags =
  match environment with
  | None -> ("cpp2v", flags)
  | Some alias ->
      let id = Names.Id.of_string alias in
      let config =
        try ComExtraDeps.query_extra_dep id with Not_found ->
          CErrors.user_err Pp.(str "cpp.prog: environment " ++ Names.Id.print id ++
            str " is not a declared Extra Dependency.")
      in
      let from = Libnames.dirpath_of_string "skylabs.lang.cpp.parser.plugin" in
      let command =
        Loadpath.find_extra_dep_with_logical_path ~from ~file:"cpp2v_inline" ()
        |> absolute_path
      in
      (command, configured_arguments command (absolute_path config) flags)

let run_cpp2v environment flags =
  let (command, flags) = cpp2v_invocation environment flags in
  match Unix.open_process_args_full command flags (Unix.environment ()) with
  | exception Unix.Unix_error(e,_,_) ->
      CErrors.user_err Pp.(str "Running command `" ++ str command ++ str "` exited with error: "
        ++ str (Unix.error_message e))
  | (_, _, stderr) as streams ->
  let stderr = In_channel.input_all stderr in
  let status = Unix.close_process_full streams in
  report_cpp2v_result flags stderr status

let make_explicit file =
  match Filename.is_implicit file with
  | true -> Filename.concat Filename.current_dir_name file
  | false -> file

let load_generated_file file =
  (* Might lead to issues with rocq-lsp if the loaded file has requires. *)
  let st = Vernacstate.freeze_full_state () in
  let command =
    let file = make_explicit file in
    let expr = Vernacexpr.(VernacSynterp (VernacLoad (false, file))) in
    CAst.make Vernacexpr.{control = []; attrs = []; expr}
  in
  ignore (Vernacinterp.interp ~intern:Vernacinterp.fs_intern ~st command)

let cpp_command_prog ((attrs : attrs), environment) name flags prog =
  match Loc.get_current_command_loc () with
  | None ->
      CErrors.user_err Pp.(str "cpp.prog needs a Rocq source file location \
        to generate stable filenames.")
  | Some(loc) ->
      let (cpp_file, v_file) = generated_filenames loc in
      let finally () =
        let remove file = try Sys.remove file with Sys_error(_) -> () in
        remove cpp_file; remove v_file
      in
      Fun.protect ~finally @@ fun _ ->
      write_cpp cpp_file prog;
      run_cpp2v environment (cpp2v_arguments attrs name cpp_file v_file flags);
      load_generated_file v_file
