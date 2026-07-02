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
    Attributes.qualify_attribute "duplicates"
    @@ attribute_of_list [
      ("warn", single_key_parser ~name ~key:"warn" Warn);
      ("error", single_key_parser ~name ~key:"error" Error);
      ("ignore", single_key_parser ~name ~key:"ignore" Ignore);
    ]
  in
  let bool_attribute name =
    map (fun x -> x = Some true) (Attributes.bool_attribute ~name)
  in
  map (fun ((((check_duplicates, elaborate), check_types), with_templates), no_templates) ->
      let with_templates =
        with_templates || not no_templates
      in
      { check_duplicates; elaborate; check_types;
        with_templates })
    (((duplicates ++ bool_attribute "elaborate") ++ bool_attribute "check_types") ++
     bool_attribute "with_templates" ++ bool_attribute "no_templates")

let lib_ref t =
  Rocqlib.lib_ref ("skylabs.lang.cpp.parser.translation_unit." ^ t)

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
  | Names.GlobRef.IndRef ind ->
    EConstr.mkIndU (ind, EConstr.EInstance.empty)
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

let cpp_command (attrs : attrs) name (abi : Constrexpr.constr_expr option) (defns : Constrexpr.constr_expr list) =
  (* Create the definition *)
  let { check_duplicates; _ } = attrs in
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
    match abi with
    | Some abi ->
      let expected_type = Pretyping.OfType (to_econstr (lib_ref "abi_type")) in
      let abi , ustate = Constrintern.interp_constr ~expected_type env evd abi in
      (abi, Evd.from_ctx ustate)
    | None ->
      (to_econstr (lib_ref "abi_default"), evd)
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
        match check_duplicates with
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
    CErrors.user_err Pp.(str "cpp.ast failed to return a head constructor. Please report!" ++ fnl () ++
                        Printer.pr_econstr_env env evd body)
