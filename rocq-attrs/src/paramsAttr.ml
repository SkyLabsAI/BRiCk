(************************************************************************)
(* Standalone plugin: a programmable [#[params="N"]] attribute.         *)
(************************************************************************)

open Names
open Globnames

let params_key = "rocq_attrs.params.type"

(* Use Rocq's registered-reference table, not user name lookup: a user may
   shadow [Params], but [Register Params as rocq_attrs.params.type] is stable. *)
let params_ref () =
  try Rocqlib.lib_ref params_key with
  | Rocqlib.NotFoundRef _ ->
    CErrors.user_err
      Pp.(str "The [Params] class is not registered; require attrs.ParamsAttr.")

let params_ind () =
  match params_ref () with
  | GlobRef.IndRef ind -> ind
  | _ ->
    CErrors.user_err
      Pp.(str "Registered [Params] reference is not an inductive class.")

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

type params_decl = {
  source : GlobRef.t;
  arity : int;
  hint_locality : Hints.hint_locality;
  definition_scope : Locality.definition_scope;
  source_poly : bool;
}

type params_terms = {
  typ : EConstr.t;
  body : EConstr.t;
}

let build_params_terms env sigma source arity =
  let sigma, of_term = Evd.fresh_global env sigma source in
  let of_type = Retyping.get_type_of env sigma of_term in
  let sigma, arity = nat_constr env sigma arity in
  let params = params_ref () in
  let ind = params_ind () in
  let sigma, params_term = Evd.fresh_global env sigma params in
  let type_args = [| of_type; of_term; arity |] in
  let typ = EConstr.mkApp (params_term, type_args) in
  let _, params_u = EConstr.destInd sigma params_term in
  let body =
    EConstr.mkApp (EConstr.mkConstructUi ((ind, params_u), 1), type_args)
  in
  sigma, { typ; body }

let declare_params_instance decl =
  let env = Global.env () in
  if not (Typeclasses.is_class env (params_ref ())) then
    CErrors.user_err Pp.(str "Registered [Params] reference is not a typeclass.");
  let sigma = Evd.from_env env in
  let sigma, terms = build_params_terms env sigma decl.source decl.arity in
  let name = instance_name decl.source in
  let cinfo = Declare.CInfo.make ~name ~typ:(Some terms.typ) () in
  let kind = Decls.(IsDefinition Instance) in
  let poly = PolyFlags.of_univ_poly decl.source_poly in
  let info = Declare.Info.make ~kind ~poly ~scope:decl.definition_scope () in
  let instance =
    Declare.declare_definition ~info ~cinfo ~opaque:false ~body:terms.body sigma
  in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  Classes.declare_instance ~warn:true env sigma
    (Some Hints.empty_hint_info) decl.hint_locality instance

let source_is_poly = function
  | GlobRef.ConstRef _ as gr -> Global.is_polymorphic gr
  | _ -> false

let final_hint_locality = function
  | Locality.Global Locality.ImportDefaultBehavior -> Hints.Export
  | Locality.Global Locality.ImportNeedQualified -> Hints.Local
  | Locality.Discharge -> Hints.Local

let should_rebuild_after_section source source_scope =
  match source, source_scope with
  | GlobRef.ConstRef _, Locality.Global Locality.ImportDefaultBehavior -> true
  | _ -> false

type discharge_data = {
  source : GlobRef.t;
  arity : int;
  final_hint_locality : Hints.hint_locality;
  final_definition_scope : Locality.definition_scope;
  source_poly : bool;
}

let declare_from_discharge data =
  (* While sections remain open, rebuild only a temporary local helper for
     in-section search; the final exported hint is installed after the last End. *)
  let still_in_section = Global.sections_are_opened () in
  declare_params_instance {
    source = data.source;
    arity = data.arity;
    hint_locality =
      if still_in_section then Hints.Local else data.final_hint_locality;
    definition_scope =
      if still_in_section then Locality.Discharge else data.final_definition_scope;
    source_poly = data.source_poly;
  }

let discharge_params_instance data =
  try
    (* Rocq reports only the section variables actually used by [source]. *)
    let used_section_vars = Array.length (Global.section_instance data.source) in
    Some { data with arity = data.arity + used_section_vars }
  with Not_found ->
    None

let rebuild_params_instance data =
  declare_from_discharge data;
  data

let subst_params_instance (subst, data) =
  let source = fst (subst_global subst data.source) in
  { data with source }

let params_instance_object =
  Libobject.declare_object
    { (Libobject.default_object "rocq-attrs params discharge") with
      Libobject.cache_function = (fun _ -> ());
      load_function = (fun _ _ -> ());
      classify_function = (fun _ -> Libobject.Substitute);
      subst_function = subst_params_instance;
      discharge_function = discharge_params_instance;
      rebuild_function = rebuild_params_instance }

let decimal_string s =
  s <> "" && String.for_all (fun c -> '0' <= c && c <= '9') s

let parse_payload ?loc previous = function
  | Attributes.VernacFlagLeaf (Attributes.FlagString s) ->
    Attributes.assert_once ?loc ~name:"params" previous;
    begin match decimal_string s, int_of_string_opt s with
    | true, Some n -> n
    | _ ->
      CErrors.user_err ?loc
        Pp.(str "Attribute params expects a non-negative decimal string, as in #[params=\"0\"].")
    end
  | _ ->
    CErrors.user_err ?loc
      Pp.(str "Attribute params expects a string payload, as in #[params=\"0\"].")

let hook n =
  Declare.Hook.make @@ fun data ->
    let source = data.Declare.Hook.S.dref in
    let source_scope = data.Declare.Hook.S.scope in
    let source_poly = source_is_poly source in
    let in_section = Global.sections_are_opened () in
    (* Let/section-local declarations are local-only: no discharge object with a
       VarRef, so user input cannot trigger the old unbound-variable anomaly. *)
    declare_params_instance {
      source;
      arity = n;
      hint_locality = if in_section then Hints.Local else final_hint_locality source_scope;
      definition_scope = if in_section then Locality.Discharge else source_scope;
      source_poly;
    };
    if in_section && should_rebuild_after_section source source_scope then
      Lib.add_leaf (params_instance_object {
        source;
        arity = n;
        final_hint_locality = final_hint_locality source_scope;
        final_definition_scope = source_scope;
        source_poly;
      })

(* The [#[params="N"]] attribute registers a [Params] typeclass instance
   when Rocq's command path calls definition hooks. In this plugin-local pass
   that means [Definition] and section [Let]; assumptions/proofs/fixpoints need
   Rocq-core hook plumbing. *)
let params_attribute : Declare.Hook.t list Attributes.attribute =
  let open Attributes in
  Notations.map
    (Option.cata (fun n -> [hook n]) [])
    (attribute_of_list ["params", parse_payload])

let params_token =
  Vernacentries.DefAttributes.Observer.register
    ~name:"params-attribute" params_attribute

let () = Vernacentries.DefAttributes.Observer.activate params_token
