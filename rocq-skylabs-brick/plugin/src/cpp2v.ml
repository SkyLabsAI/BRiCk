(*
 * Copyright (c) 2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
open Procq.Constr
open Stdarg

type report_level =
  | Ignore
  | Warn
  | Error

let attributes =
  let open Attributes in
  let name = "duplicates" in
  (Attributes.qualify_attribute "duplicates"
    @@ attribute_of_list [
        ("warn", single_key_parser ~name ~key:"warn" Warn);
        ("error", single_key_parser ~name ~key:"error" Error);
        ("ignore", single_key_parser ~name ~key:"ignore" Ignore);
    ])

let lib_ref t =
  Rocqlib.lib_ref ("bluerock.lang.cpp.parser.translation_unit." ^ t)

let (cpp2v_category, cpp2v_warning) =
  CWarnings.create_hybrid ~name:"cpp2v" ()

let duplicate_symbols : (Environ.env * Evd.evar_map * Evd.econstr) CWarnings.msg = CWarnings.create_msg cpp2v_warning ()

let duplicate_symbols_printer (env, evd, err) =
  Pp.(str "Duplicate symbols found!" ++ fnl () ++ Printer.pr_econstr_env env evd err ++ str ".")

let _ =
  CWarnings.register_printer duplicate_symbols duplicate_symbols_printer

let to_econstr t =
  match t with
  | Names.GlobRef.ConstRef c ->
    EConstr.mkConstU (c, EConstr.EInstance.empty)
  | _ ->
    Feedback.msg_debug Pp.(Names.GlobRef.print t) ;
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

let cpp_command (attrs : report_level option) name (abi : Constrexpr.constr_expr) (defns : Constrexpr.constr_expr list) =
  (* Create the definition *)
  let env = Global.env() in
  let e_decl = to_econstr (lib_ref "t") in
  let e_decl_skip = to_econstr (lib_ref "skip") in
  let inst =
    match Constr.kind (decl_of_ref "empty_array").const_type with
    | Constr.App (f, _) ->
      begin
        match Constr.kind f with
        | Constr.Const (_, univs) -> univs
        | _ -> assert false
      end
    | _ -> assert false
  in
  let evd = Evd.from_env env in
  let abi , evd =
    let expected_type = Pretyping.OfType (to_econstr (lib_ref "abi_type")) in
    let abi , ustate = Constrintern.interp_constr ~expected_type env evd abi in
    (abi, Evd.from_ctx ustate)
  in
  let body , evd =
    let expected_type = Pretyping.OfType e_decl in
    List.fold_left (fun (acc, evd) defn ->
        (* TODO: the docs say that i should not use this function,
           but it doesn't seem like i can give an expected type to
           [Constrintern.interp_constr_evars] *)
        let body, ustate = Constrintern.interp_constr ~expected_type env evd defn in
        (body :: acc, Evd.from_ctx ustate)) ([], evd) defns
  in
  let body =
    EConstr.mkArray (EConstr.EInstance.make inst, Array.of_list (List.rev body), e_decl_skip, e_decl)
  in
  let body =
    EConstr.mkApp (to_econstr (lib_ref "decls"), [| body ; abi |])
  in
  let body =
    let rt = force_body (decl_of_ref "result_type") in
    Vnorm.cbv_vm env evd body (EConstr.of_constr rt)
  in
  (* The term should have type <<translation_unit.t * dup_info>>
     where <<dup_info>> is a list.
   *)
  match EConstr.kind evd body with
  | Constr.App (hd, [| _ ; _ ; body ; err |]) when EConstr.isConstruct evd hd ->
    let _ =
      match EConstr.kind evd err with
      | Constr.App (hd, [| _ |]) when EConstr.isConstruct evd hd ->
        (* This is matching for [nil] *)
        ()
      | _ ->
        begin
        match attrs with
        | Some Error -> CErrors.user_err @@ duplicate_symbols_printer (env, evd, err)
        | Some Warn -> CWarnings.warn duplicate_symbols (env, evd, err)
        | Some Ignore | None -> ()
        end
    in
    let cinfo = Declare.CInfo.make ~name ~typ:None () in
    let info = Declare.Info.make () in
    let _ =
      Declare.declare_definition ~info ~cinfo ~opaque:false ~body evd
    in
    ()
  | _ ->
    CErrors.user_err Pp.(str "cpp.prog failed to return a head constructor. Please report!" ++ fnl () ++
                        Printer.pr_econstr_env env evd body)

let temp_file ?(prefix="ocaml_temp_") ?(suffix=".tmp") content =
    (* Generate a unique temporary file name *)
    let temp_file = Filename.temp_file prefix suffix in

    (* Open the file for writing *)
    let oc = open_out temp_file in

    try
      (* Write the content to the file *)
      output_string oc content;

      (* Flush and close the file *)
      flush oc;
      close_out oc;

      let unlink () =
        try Sys.remove temp_file
        with _ -> ()
      in

      (* Return the path to the created temporary file *)
      temp_file , unlink
    with e ->
      (* Clean up in case of an exception *)
      close_out_noerr oc;
      let _ = try Sys.remove temp_file with _ -> () in
      raise e

let cpp_command_prog (attrs : report_level option) name flags prog =
  let temp_cpp , unlink = temp_file ~suffix:".cpp" prog in
  let temp_v = Filename.temp_file "_" ".v" in
  let flags =
    let flags =
      match flags with
      | None -> []
      | Some flags ->
        Feedback.msg_notice Pp.(str "Note that cpp.prog does not guarantee the working directory," ++ Pp.brk (0,0) ++
                                str "so relative paths may yield inconsistent results between different editors." ++ fnl () ++
                               str "Current working directory: " ++ str (Unix.getcwd ())) ;
        Str.split (Str.regexp "[ \n\r\x0c\t]+") flags
    in
    ["cpp2v";
    "-for-interactive"; Names.Id.to_string name;
    "--no-sharing"; (* to avoid polluting the namespace. It would be better to put this in a [Module]
                         if we are not in a [Section] *)
    "-o"; temp_v;
    temp_cpp] @
    (match attrs with
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
    let stdin , stdout , stderr = streams in

    (* Read all output *)
    let rec read_all channel buffer =
      try
        let line = input_line channel in
        Buffer.add_string buffer line;
        Buffer.add_char buffer '\n';
        read_all channel buffer
      with End_of_file -> buffer
    in

    (* Capture stdout and stderr *)
    let stderr_buffer = Buffer.create 4096 |> read_all stderr in
    let msg_text (warn_err : string) (cpp2v_stderr : string) =
      Pp.(
        str "Invoking cpp2v " ++ str warn_err ++ fnl() ++
        str cpp2v_stderr ++ fnl() ++
        str "cpp2v command line:" ++ fnl() ++ str "  " ++ prlist_with_sep (fun () -> str " ") str flags)
    in
    let process_status = Unix.close_process_full streams in
    let success =
      match process_status with
      | WEXITED 0 -> true
      | _ -> false
    in
    if not success then
      if Buffer.length stderr_buffer = 0 then
        CErrors.user_err Pp.(msg_text "failed with no error message!" "")
      else
        CErrors.user_err Pp.(msg_text "failed with the following warnings/errors!" (Buffer.contents stderr_buffer))
    else if Buffer.length stderr_buffer > 0 then
      Feedback.msg_warning Pp.(msg_text "produced the following warnings!" (Buffer.contents stderr_buffer));

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
   If we need to avoid using <<Load>>, e.g. to suport coq-lsp, then we can use
   this structure.

  see: toplevel/vernac.ml:105
  let source = Option.default (Loc.InFile {dirpath=None; file}) source in
  let in_pa = Procq.Parsable.make ~loc:Loc.(initial source)
      (Gramlib.Stream.of_channel stdout) in

  (* I can loop this until it says None *)
  Procq.Entry.parse (Pvernac.main_entry None) in_pa

  assert false
*)
