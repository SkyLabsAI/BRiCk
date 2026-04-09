
open Ltac2_plugin
open Tac2ffi
(* open Tac2val *)
open Tac2externals

let fresh_type_scheme env (t : Tac2expr.type_scheme) : Tac2typing_env.TVar.t Tac2expr.glb_typexpr =
  let open Tac2typing_env in
  let (n, t) = t in
  let subst = Array.init n (fun _ -> fresh_id env) in
  let substf i = Tac2expr.GTypVar subst.(i) in
  subst_type substf t

let target_type : n_args:int -> Tac2expr.type_scheme =
  let open Tac2expr in
  let unit = GTypRef (Tuple 0, []) in
  fun ~n_args ->
  let constr =
    let mp = Tac2env.rocq_prefix in
    let id = Names.Label.of_id @@ Names.Id.of_string_soft "constr" in
    let name = Names.KerName.make mp id in
    GTypRef (Other name, [])
  in
  let rec go n_args =
    if n_args == 0 then
      GTypArrow (unit, unit)
    else
      GTypArrow (constr, go (n_args - 1))
  in
  (0, go n_args)

let pr_closed_type : Tac2expr.type_scheme -> Pp.t = fun t ->
  let open Tac2typing_env in
  let env = Tac2typing_env.empty_env ~strict:true () in
  let (n, t) = t in
  let subst = Array.init n (fun _ -> fresh_id env) in
  let substf i = Tac2expr.GTypVar subst.(i) in
  let t = subst_type substf t in
  Tac2typing_env.pr_glbtype env t

type type_mismatch = {
  name: Names.KerName.t;
  actual_type: Tac2expr.type_scheme;
  expected_type: Tac2expr.type_scheme
}

let category = CWarnings.create_category ~name:"ltac2-tc-dispatch" ()

let type_mismatch =
  let warn {name; actual_type; expected_type} =
    Pp.(str "Ltac2 tactic " ++ Names.KerName.print name ++ str " has type " ++
        pr_closed_type actual_type ++ str " but was expected to have type " ++
        pr_closed_type expected_type)
  in
  CWarnings.create
    ~category
    ~default:CWarnings.AsError
    ~name:"ltac2-tc-dispatch-type-mismatch"
    warn

exception NoSuchGlobal of Names.KerName.t
exception TypeMismatch of type_mismatch

let resolve_ltac2_safe (r : Names.GlobRef.t) (args : Tac2val.valexpr list) : (unit -> unit Proofview.tactic) option Proofview.tactic =
  let path =
    let open Names.GlobRef in
    match r with
    | ConstRef(c) -> Some(Names.Constant.canonical c)
    (* | IndRef(c) -> Some(Names.Ind.modpath c, Names.MutInd.user (fst c)) *)
    | _ -> None
  in
  match path with
  | None ->
    (* Feedback.msg_debug Pp.(str "could not find constant in reference " ++ Names.GlobRef.print r); *)
    Proofview.tclUNIT None
  | Some path ->
  let n_args = List.length args in
  let check_type name (actual_type : Tac2expr.type_scheme) : unit =
    (* Feedback.msg_debug Pp.(str "ty: " ++ pr_closed_type ty); *)
    let expected_type = target_type ~n_args in
    (* Feedback.msg_debug Pp.(str "tty: " ++ pr_closed_type (0, tty)); *)
    if not @@ Tac2intern.check_subtype actual_type expected_type then
      raise (TypeMismatch {name; actual_type; expected_type})
  in
  try
    let data = try Tac2env.interp_global path with | Not_found as e ->
      let (_, info) = Exninfo.capture e in
      Exninfo.iraise ((NoSuchGlobal path, info))
    in
    (* Feedback.msg_debug Pp.(str "checking types"); *)
    check_type path data.Tac2env.gdata_type;
    let v = Tac2interp.eval_global path in
    (* Feedback.msg_debug Pp.(str "building application"); *)
    let v = Tac2val.apply_val v args in
    (* Feedback.msg_debug Pp.(str "applying"); *)
    let open Proofview.Notations in
    v >>= fun v ->
    (* Feedback.msg_debug Pp.(str "applied!"); *)
    Proofview.tclUNIT (Some (repr_to (fun1 unit unit) v))
  with
  | TypeMismatch m ->
    type_mismatch m;
    (* let () = Feedback.msg_debug Pp.(str "tactic type incorrect") in *)
    Proofview.tclUNIT None
  | NoSuchGlobal _path ->
    (* let () = Feedback.msg_debug Pp.(str "could not find tactic at " ++ Names.KerName.print path) in *)
    Proofview.tclUNIT None


let define s =
  define Tac2expr.{ mltac_plugin = "ltac2_tc_dispatch"; mltac_tactic = s }

let () =
  define "resolve_ltac2"
    (reference @-> list valexpr @-> tac (option (fun1 unit unit))) @@
    resolve_ltac2_safe
