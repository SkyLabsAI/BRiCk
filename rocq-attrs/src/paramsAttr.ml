(************************************************************************)
(* Standalone plugin: a programmable [#[params="N"]] attribute.         *)
(************************************************************************)

open Names
open Globnames

let params_ref () =
  Smartlocate.global_with_alias (Libnames.qualid_of_string "Params")

let nat_ref name =
  Rocqlib.lib_ref ("num.nat." ^ name)

let rec nat_constr env sigma = function
  | n when n < 0 ->
    CErrors.user_err Pp.(str "params arity must be non-negative.")
  | 0 ->
    Evd.fresh_global env sigma (nat_ref "O")
  | n ->
    let sigma, succ = Evd.fresh_global env sigma (nat_ref "S") in
    let sigma, pred = nat_constr env sigma (n - 1) in
    sigma, EConstr.mkApp (succ, [| pred |])

let instance_name gr =
  let base = Nametab.basename_of_global gr in
  let name = Nameops.add_suffix base "_params" in
  Namegen.next_global_ident_away (Global.safe_env ()) name Id.Set.empty

let declare_params_instance gr n =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, of_term = Evd.fresh_global env sigma gr in
  let of_type = Retyping.get_type_of env sigma of_term in
  let sigma, arity = nat_constr env sigma n in
  let params = params_ref () in
  let ind =
    match params with
    | GlobRef.IndRef ind -> ind
    | _ ->
      CErrors.user_err Pp.(str "Params is not an inductive typeclass.")
  in
  let sigma, params_term = Evd.fresh_global env sigma params in
  let type_args = [| of_type; of_term; arity |] in
  let typ = EConstr.mkApp (params_term, type_args) in
  let _, params_u = EConstr.destInd sigma params_term in
  let body =
    EConstr.mkApp (EConstr.mkConstructUi ((ind, params_u), 1), type_args)
  in
  let name = instance_name gr in
  let cinfo = Declare.CInfo.make ~name ~typ:(Some typ) () in
  let kind = Decls.(IsDefinition Instance) in
  let info = Declare.Info.make ~kind () in
  let instance = Declare.declare_definition ~info ~cinfo ~opaque:false ~body sigma in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let locality =
    if Global.sections_are_opened () then Hints.Local else Hints.SuperGlobal
  in
  Classes.declare_instance env sigma (Some Hints.empty_hint_info) locality instance

let discharge_params_instance (gr, n) =
  try
    let used_section_vars = Array.length (Global.section_instance gr) in
    Some (gr, n + used_section_vars)
  with Not_found ->
    None

let rebuild_params_instance (gr, n) =
  declare_params_instance gr n;
  (gr, n)

let subst_params_instance (subst, (gr, n)) =
  fst (subst_global subst gr), n

let params_instance_object =
  Libobject.declare_object
    { (Libobject.default_object "rocq-attrs params discharge") with
      Libobject.cache_function = (fun _ -> ());
      load_function = (fun _ _ -> ());
      classify_function = (fun _ -> Libobject.Substitute);
      subst_function = subst_params_instance;
      discharge_function = discharge_params_instance;
      rebuild_function = rebuild_params_instance }

let parse_payload ?loc previous = function
  | Attributes.VernacFlagLeaf (Attributes.FlagString s) ->
    Attributes.assert_once ?loc ~name:"params" previous;
    begin match int_of_string_opt s with
    | Some n when n >= 0 -> n
    | _ ->
      CErrors.user_err ?loc
        Pp.(str "Attribute params expects a non-negative integer string.")
    end
  | _ ->
    CErrors.user_err ?loc
      Pp.(str "Attribute params expects a string payload, as in #[params=\"0\"].")

let hook n =
  Declare.Hook.make @@ fun data ->
    let gr = data.Declare.Hook.S.dref in
    declare_params_instance gr n;
    if Global.sections_are_opened () then
      Lib.add_leaf (params_instance_object (gr, n))

(* The [#[params="N"]] attribute registers a [Params] typeclass instance
   for the annotated definition. *)
let params_attribute : Declare.Hook.t list Attributes.attribute =
  let open Attributes in
  Notations.map
    (Option.cata (fun n -> [hook n]) [])
    (attribute_of_list ["params", parse_payload])

let params_token =
  Vernacentries.DefAttributes.Observer.register
    ~name:"params-attribute" params_attribute

let () = Vernacentries.DefAttributes.Observer.activate params_token
