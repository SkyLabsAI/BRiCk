Require Import skylabs.lang.cpp.syntax.source_location.
Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.mparser.
Require Import skylabs.lang.cpp.parser.source_location.

#[local] Open Scope pstring_scope.

Definition root_name : name := Nglobal (Nid "selected").
Definition int_type : type := Tnum int_rank.Iint Signed.
Definition bool_type : type := Tbool.
Definition int_value : ObjValue :=
  Ovar int_type (global_init.Init (Eint 0 int_type)).
Definition extern_value : ObjValue := Ovar int_type global_init.Extern.
Definition bool_value : ObjValue := Ovar bool_type global_init.NoInit.
Definition leaf (ids : list origin_id) : loc_tree origin_id := LocNode ids [].
Definition old_tree : loc_tree origin_id := LocNode [0] [leaf [3]].
Definition new_tree : loc_tree origin_id := LocNode [1] [leaf [2]].

Definition event_symbol
    (events : list Construction.located_root_event) :
    Construction.construction_error + option ObjValue :=
  match Construction.fold_events_from events Construction.empty_state with
  | inl error => inl error
  | inr state => inr (fst <$> state.(Construction.state_symbols) !! root_name)
  end.

Definition event_type
    (events : list Construction.located_root_event) :
    Construction.construction_error + option GlobDecl :=
  match Construction.fold_events_from events Construction.empty_state with
  | inl error => inl error
  | inr state => inr (fst <$> state.(Construction.state_types) !! root_name)
  end.

Definition event_msymbol
    (events : list Construction.located_root_event) :
    Construction.construction_error + option (template MObjValue) :=
  match Construction.fold_events_from events Construction.empty_state with
  | inl error => inl error
  | inr state => inr (fst <$> state.(Construction.state_msymbols) !! root_name)
  end.

Definition parsed_symbol (declarations : list translation_unit.t) :
    option ObjValue :=
  let '(unit, _) :=
    translation_unit.list_decls declarations abi.abi_default in
  unit.(symbols) !! root_name.

Definition parsed_type (declarations : list translation_unit.t) :
    option GlobDecl :=
  let '(unit, _) :=
    translation_unit.list_decls declarations abi.abi_default in
  unit.(types) !! root_name.

Definition parsed_msymbol (declarations : list Mtranslation_unit.t) :
    option (template MObjValue) :=
  (Mtranslation_unit.decls declarations).(templates.msymbols) !! root_name.

Definition symbol_tree (events : list Construction.located_root_event) :
    option (loc_tree origin_id) :=
  match Construction.fold_events events with
  | inl _ => None
  | inr locations => locations.(symbol_locations) !! root_name
  end.

Definition type_tree (events : list Construction.located_root_event) :
    option (loc_tree origin_id) :=
  match Construction.fold_events events with
  | inl _ => None
  | inr locations => locations.(type_locations) !! root_name
  end.

Definition msymbol_tree (events : list Construction.located_root_event) :
    option (loc_tree origin_id) :=
  match Construction.fold_events events with
  | inl _ => None
  | inr locations => locations.(msymbol_locations) !! root_name
  end.

Definition equal_events :=
  [ Construction.LESymbol root_name int_value old_tree
  ; Construction.LESymbol root_name int_value new_tree
  ].

Example equal_duplicates_select_the_parser_value :
    event_symbol equal_events =
      inr (parsed_symbol
        [Dobj_value root_name int_value; Dobj_value root_name int_value]).
Proof. vm_compute. reflexivity. Qed.

Example equal_duplicates_merge_the_selected_tree :
    symbol_tree equal_events = Some (LocNode [1; 0] [leaf [2; 3]]).
Proof. vm_compute. reflexivity. Qed.

Definition compatible_events :=
  [ Construction.LESymbol root_name extern_value old_tree
  ; Construction.LESymbol root_name int_value new_tree
  ].

Example compatible_duplicates_select_the_parser_value :
    event_symbol compatible_events =
      inr (parsed_symbol
        [Dobj_value root_name extern_value; Dobj_value root_name int_value]).
Proof. vm_compute. reflexivity. Qed.

Example compatible_duplicates_select_the_winner_tree :
    symbol_tree compatible_events = Some (LocNode [1; 0] [leaf [2]]).
Proof. vm_compute. reflexivity. Qed.

Definition self_typedef_events :=
  [Construction.LEType root_name (Gtypedef (Tnamed root_name)) old_tree].

Example self_typedef_matches_parser_suppression :
    event_type self_typedef_events =
      inr (parsed_type
        [Dglob_decl root_name (Gtypedef (Tnamed root_name))]).
Proof. vm_compute. reflexivity. Qed.

Example self_typedef_has_no_location_root :
    type_tree self_typedef_events = None.
Proof. vm_compute. reflexivity. Qed.

Definition old_template : template MObjValue := Template [] int_value.
Definition new_template : template MObjValue := Template [] bool_value.
Definition template_events :=
  [ Construction.LEMsymbol root_name old_template old_tree
  ; Construction.LEMsymbol root_name new_template new_tree
  ].

Example template_overwrite_selects_the_parser_value :
    event_msymbol template_events =
      inr (parsed_msymbol
        [ Dtemplated_obj_value root_name old_template
        ; Dtemplated_obj_value root_name new_template
        ]).
Proof. vm_compute. reflexivity. Qed.

Example template_overwrite_selects_the_later_tree :
    msymbol_tree template_events = Some (LocNode [1; 0] [leaf [2]]).
Proof. vm_compute. reflexivity. Qed.
