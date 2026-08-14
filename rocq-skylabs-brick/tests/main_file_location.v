(* Copyright (c) 2026 SkyLabs AI, Inc. *)
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.syntax.source_location.
Require Import skylabs.lang.cpp.syntax.mcore.
Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.mparser.tu.
Require Import skylabs.lang.cpp.parser.source_location.
Require Import skylabs.prelude.parray.
Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Import skylabs_brick.tests.source_location.

Import core.
#[local] Open Scope uint63_scope.
Import source_location.

Definition no_location : Construction.indexed_location_presence := {|
  Construction.indexed_presence_at_root := false;
  Construction.indexed_presence_in_tree := false
|}.

Definition nested_location : Construction.indexed_location_presence := {|
  Construction.indexed_presence_at_root := false;
  Construction.indexed_presence_in_tree := true
|}.

Definition root_location : Construction.indexed_location_presence := {|
  Construction.indexed_presence_at_root := true;
  Construction.indexed_presence_in_tree := true
|}.

Example filtered_loser_nested_location_does_not_survive_add_root :
  Construction.add_losing_indexed_presence no_location nested_location =
  no_location.
Proof. vm_compute. reflexivity. Qed.

Example filtered_loser_root_location_survives_add_root :
  Construction.add_losing_indexed_presence no_location root_location =
  root_location.
Proof. vm_compute. reflexivity. Qed.

Example filtered_equal_duplicate_merges_nested_presence :
  Construction.merge_indexed_presence no_location nested_location =
  nested_location.
Proof. vm_compute. reflexivity. Qed.

Definition filtered_type_event (value : GlobDecl)
    (at_root in_tree : bool)
    : Construction.filtered_indexed_located_root_event :=
  Construction.FILEType shared_root_name value
    0%uint63 0%uint63 at_root in_tree.

Definition filtered_symbol_event (value : ObjValue)
    (at_root in_tree : bool)
    : Construction.filtered_indexed_located_root_event :=
  Construction.FILESymbol shared_root_name value
    0%uint63 0%uint63 at_root in_tree.

Definition filtered_msymbol_event (value : template MObjValue)
    (at_root in_tree : bool)
    : Construction.filtered_indexed_located_root_event :=
  Construction.FILEMsymbol shared_root_name value
    0%uint63 0%uint63 at_root in_tree.

Definition filtered_mtype_event (value : template MGlobDecl)
    (at_root in_tree : bool)
    : Construction.filtered_indexed_located_root_event :=
  Construction.FILEMtype shared_root_name value
    0%uint63 0%uint63 at_root in_tree.

Definition filtered_at
    (events : list Construction.filtered_indexed_located_root_event)
    (root : decl_root) : option indexed_location :=
  match Construction.fold_filtered_indexed_events events with
  | inl _ => None
  | inr locations => Internal.find_root locations root
  end.

Example filtered_fold_omits_final_empty_residual_root :
  filtered_at [filtered_type_event (Gtypedef int_type) false false]
    (DRType shared_root_name) = None.
Proof. vm_compute. reflexivity. Qed.

Example filtered_fold_retains_final_root_location :
  filtered_at [filtered_type_event (Gtypedef int_type) true true]
    (DRType shared_root_name) = Some (StaticLocation 0%uint63 0%uint63).
Proof. vm_compute. reflexivity. Qed.

Example filtered_equal_duplicate_keeps_losing_nested_presence :
  filtered_at
    [ filtered_symbol_event test_obj_value false false
    ; filtered_symbol_event test_obj_value false true
    ] (DRSymbol shared_root_name) =
  Some (MergeLocations 0%uint63
    (StaticLocation 0%uint63 0%uint63)
    (StaticLocation 0%uint63 0%uint63)).
Proof. vm_compute. reflexivity. Qed.

Example filtered_ordinary_losing_nested_presence_is_omitted :
  filtered_at
    [ filtered_symbol_event indexed_extern_obj_value false true
    ; filtered_symbol_event test_obj_value false false
    ] (DRSymbol shared_root_name) = None.
Proof. vm_compute. reflexivity. Qed.

Example filtered_ordinary_losing_root_presence_is_retained :
  filtered_at
    [ filtered_symbol_event indexed_extern_obj_value true true
    ; filtered_symbol_event test_obj_value false false
    ] (DRSymbol shared_root_name) =
  Some (AddRootOrigins 0%uint63
    (StaticLocation 0%uint63 0%uint63)
    (StaticLocation 0%uint63 0%uint63)).
Proof. vm_compute. reflexivity. Qed.

Example filtered_ordinary_winner_nested_presence_is_retained :
  filtered_at
    [ filtered_symbol_event indexed_extern_obj_value false false
    ; filtered_symbol_event test_obj_value false true
    ] (DRSymbol shared_root_name) =
  Some (AddRootOrigins 0%uint63
    (StaticLocation 0%uint63 0%uint63)
    (StaticLocation 0%uint63 0%uint63)).
Proof. vm_compute. reflexivity. Qed.

Example filtered_self_alias_is_suppressed :
  filtered_at
    [filtered_type_event (Gtypedef (Tnamed shared_root_name)) true true]
    (DRType shared_root_name) = None.
Proof. vm_compute. reflexivity. Qed.

Example filtered_incompatible_duplicates_preserve_the_error :
  Construction.fold_filtered_indexed_events
    [ filtered_type_event (Gtypedef int_type) true true
    ; filtered_type_event (Gtypedef bool_type) false false
    ] = inl (Construction.IncompatibleDuplicates
      [(shared_root_name, inl (Gtypedef int_type));
       (shared_root_name, inl (Gtypedef bool_type))]).
Proof. vm_compute. reflexivity. Qed.

Definition old_template_value : template MObjValue :=
  Template [] indexed_extern_obj_value.
Definition new_template_value : template MObjValue :=
  Template [] test_obj_value.

Example filtered_template_losing_nested_presence_is_omitted :
  filtered_at
    [ filtered_msymbol_event old_template_value false true
    ; filtered_msymbol_event new_template_value false false
    ] (DRMsymbol shared_root_name) = None.
Proof. vm_compute. reflexivity. Qed.

Example filtered_template_losing_root_presence_is_retained :
  filtered_at
    [ filtered_msymbol_event old_template_value true true
    ; filtered_msymbol_event new_template_value false false
    ] (DRMsymbol shared_root_name) =
  Some (AddRootOrigins 0%uint63
    (StaticLocation 0%uint63 0%uint63)
    (StaticLocation 0%uint63 0%uint63)).
Proof. vm_compute. reflexivity. Qed.

Example filtered_template_type_direction_keeps_later_nested_presence :
  filtered_at
    [ filtered_mtype_event (Template [] Gtype) false false
    ; filtered_mtype_event (Template [] (Gtypedef int_type)) false true
    ] (DRMtype shared_root_name) =
  Some (AddRootOrigins 0%uint63
    (StaticLocation 0%uint63 0%uint63)
    (StaticLocation 0%uint63 0%uint63)).
Proof. vm_compute. reflexivity. Qed.
