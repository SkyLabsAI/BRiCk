(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.syntax.source_location.
Require Import skylabs.lang.cpp.syntax.mcore.
Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.mparser.tu.
Require Import skylabs.lang.cpp.parser.source_location.
Require Import skylabs.prelude.parray.
Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Import Stdlib.ZArith.ZArith.

#[local] Notation lookup := syntax.source_location.lookup (only parsing).

Definition test_origin
    (kind : origin_kind) (anchor : option origin_id)
    (derived : list origin_id) : source_origin := {|
  origin_class := kind;
  spelling_range := None;
  expansion_range := None;
  presumed_begin := None;
  presumed_end := None;
  macro_stack := [];
  point_of_instantiation := None;
  anchor_origin := anchor;
  derived_from := derived
|}.

Definition origin0 : source_origin := test_origin ExplicitOrigin None [].
Definition origin1 : source_origin := test_origin ImplicitOrigin None [].
Definition origin2 : source_origin := test_origin ClangTransformedOrigin None [].
Definition origin3 : source_origin := test_origin Cpp2vSynthesizedOrigin None [].
Definition test_origins : list source_origin :=
  [origin0; origin1; origin2; origin3].

Definition shared_root_name : name := "shared()"%cpp_name.
Definition absent_root_name : name := "absent()"%cpp_name.

Definition leaf (ids : list origin_id) : loc_tree origin_id :=
  LocNode ids [].

Definition namespace_locations : declaration_locations origin_id := {|
  symbol_locations := <[shared_root_name := leaf [0]]> ∅;
  type_locations := <[shared_root_name := leaf [1]]> ∅;
  msymbol_locations := <[shared_root_name := leaf [2]]> ∅;
  mtype_locations := <[shared_root_name := leaf [3]]> ∅
|}.

Definition namespace_map : source_map := {|
  files := [];
  origin_data := ExpandedOrigins test_origins;
  declarations := namespace_locations
|}.

Example lookup_symbol_namespace :
  lookup namespace_map (DRSymbol shared_root_name) [] = inr [origin0].
Proof. vm_compute. reflexivity. Qed.

Example lookup_type_namespace :
  lookup namespace_map (DRType shared_root_name) [] = inr [origin1].
Proof. vm_compute. reflexivity. Qed.

Example lookup_msymbol_namespace :
  lookup namespace_map (DRMsymbol shared_root_name) [] = inr [origin2].
Proof. vm_compute. reflexivity. Qed.

Example lookup_mtype_namespace :
  lookup namespace_map (DRMtype shared_root_name) [] = inr [origin3].
Proof. vm_compute. reflexivity. Qed.

Definition nested_tree : loc_tree origin_id :=
  LocNode [0] [leaf [1]; LocNode [] [leaf [2]]].

Definition nested_map : source_map := {|
  files := [];
  origin_data := ExpandedOrigins test_origins;
  declarations := {|
    symbol_locations := <[shared_root_name := nested_tree]> ∅;
    type_locations := ∅;
    msymbol_locations := ∅;
    mtype_locations := ∅
  |}
|}.

Example lookup_empty_path :
  lookup nested_map (DRSymbol shared_root_name) [] = inr [origin0].
Proof. vm_compute. reflexivity. Qed.

Example lookup_deep_path :
  lookup nested_map (DRSymbol shared_root_name) [1; 0] = inr [origin2].
Proof. vm_compute. reflexivity. Qed.

Example lookup_empty_origins_is_success :
  lookup nested_map (DRSymbol shared_root_name) [1] = inr [].
Proof. vm_compute. reflexivity. Qed.

Example lookup_missing_root :
  lookup nested_map (DRSymbol absent_root_name) [] =
    inl (RootNotFound (DRSymbol absent_root_name)).
Proof. vm_compute. reflexivity. Qed.

Example lookup_bad_child_at_root :
  lookup nested_map (DRSymbol shared_root_name) [2] =
    inl (ChildOutOfBounds (DRSymbol shared_root_name) 0 2 2).
Proof. vm_compute. reflexivity. Qed.

Example lookup_bad_child_after_prefix :
  lookup nested_map (DRSymbol shared_root_name) [1; 1] =
    inl (ChildOutOfBounds (DRSymbol shared_root_name) 1 1 1).
Proof. vm_compute. reflexivity. Qed.

Definition invalid_id_map : source_map := {|
  files := [];
  origin_data := ExpandedOrigins test_origins;
  declarations := {|
    symbol_locations := <[shared_root_name := leaf [1; 9; 8]]> ∅;
    type_locations := ∅;
    msymbol_locations := ∅;
    mtype_locations := ∅
  |}
|}.

Example lookup_reports_first_invalid_origin_id :
  lookup invalid_id_map (DRSymbol shared_root_name) [] =
    inl (OriginIdOutOfBounds (DRSymbol shared_root_name) [] 9).
Proof. vm_compute. reflexivity. Qed.

Definition invalid_anchor_origin : source_origin :=
  test_origin InheritedOrigin (Some 7) [].

Definition invalid_anchor_map : source_map := {|
  files := [];
  origin_data := ExpandedOrigins [invalid_anchor_origin];
  declarations := {|
    symbol_locations := <[shared_root_name := leaf [0]]> ∅;
    type_locations := ∅;
    msymbol_locations := ∅;
    mtype_locations := ∅
  |}
|}.

Example lookup_rejects_invalid_anchor_id :
  lookup invalid_anchor_map (DRSymbol shared_root_name) [] =
    inl (OriginIdOutOfBounds (DRSymbol shared_root_name) [] 7).
Proof. vm_compute. reflexivity. Qed.

Definition invalid_derived_origin : source_origin :=
  test_origin ClangTransformedOrigin None [6; 5].

Definition invalid_derived_map : source_map := {|
  files := [];
  origin_data := ExpandedOrigins [invalid_derived_origin];
  declarations := {|
    symbol_locations := <[shared_root_name := leaf [0]]> ∅;
    type_locations := ∅;
    msymbol_locations := ∅;
    mtype_locations := ∅
  |}
|}.

Example lookup_rejects_first_invalid_derivation_id :
  lookup invalid_derived_map (DRSymbol shared_root_name) [] =
    inl (OriginIdOutOfBounds (DRSymbol shared_root_name) [] 6).
Proof. vm_compute. reflexivity. Qed.

Definition valid_reference_origin : source_origin :=
  test_origin InheritedOrigin (Some 0) [0].

Definition valid_reference_map : source_map := {|
  files := [];
  origin_data := ExpandedOrigins [origin0; valid_reference_origin];
  declarations := {|
    symbol_locations := <[shared_root_name := leaf [1]]> ∅;
    type_locations := ∅;
    msymbol_locations := ∅;
    mtype_locations := ∅
  |}
|}.

Example lookup_accepts_valid_anchor_and_derivation_ids :
  lookup valid_reference_map (DRSymbol shared_root_name) [] =
    inr [valid_reference_origin].
Proof. vm_compute. reflexivity. Qed.

Definition ordered_multi_origin_map : source_map := {|
  files := [];
  origin_data := ExpandedOrigins test_origins;
  declarations := {|
    symbol_locations := <[shared_root_name := leaf [2; 0; 3; 1]]> ∅;
    type_locations := ∅;
    msymbol_locations := ∅;
    mtype_locations := ∅
  |}
|}.

Example lookup_preserves_explicit_multi_origin_order :
  lookup ordered_multi_origin_map (DRSymbol shared_root_name) [] =
    inr [origin2; origin0; origin3; origin1].
Proof. vm_compute. reflexivity. Qed.

Definition indexed_table_of_list {A : Type}
    (default : A) (values : list A) : Encoded.indexed_table A :=
  Encoded.Build_indexed_table
    (Uint63.of_Z (Z.of_nat (List.length values)))
    (PArray.of_list (PArray.of_list default [])
      [PArray.of_list default values]).

Definition simple_encoded_origins : list Encoded.encoded_origin :=
  [ Encoded.Build_encoded_origin ExplicitOrigin
      None None None None [] None None []
  ; Encoded.Build_encoded_origin ImplicitOrigin
      None None None None [] None None []
  ; Encoded.Build_encoded_origin ClangTransformedOrigin
      None None None None [] None None []
  ; Encoded.Build_encoded_origin Cpp2vSynthesizedOrigin
      None None None None [] None None []
  ].

Definition simple_indexed_provenance : Encoded.indexed_provenance :=
  Encoded.Build_indexed_provenance
    (indexed_table_of_list Encoded.default_presumed_filename [])
    (indexed_table_of_list Encoded.default_physical_point [])
    (indexed_table_of_list Encoded.default_encoded_presumed_point [])
    (indexed_table_of_list Encoded.default_encoded_range [])
    (indexed_table_of_list Encoded.default_encoded_macro_frame [])
    (indexed_table_of_list Encoded.default_encoded_origin
      simple_encoded_origins).

Definition indexed_namespace_map : source_map := {|
  files := [];
  origin_data := IndexedOrigins simple_indexed_provenance;
  declarations := namespace_locations
|}.

Example indexed_lookup_symbol_namespace_parity :
  lookup indexed_namespace_map (DRSymbol shared_root_name) [] =
    lookup namespace_map (DRSymbol shared_root_name) [].
Proof. vm_compute. reflexivity. Qed.

Example indexed_lookup_type_namespace_parity :
  lookup indexed_namespace_map (DRType shared_root_name) [] =
    lookup namespace_map (DRType shared_root_name) [].
Proof. vm_compute. reflexivity. Qed.

Example indexed_lookup_template_namespaces_parity :
  ( lookup indexed_namespace_map (DRMsymbol shared_root_name) []
  , lookup indexed_namespace_map (DRMtype shared_root_name) [] ) =
  ( lookup namespace_map (DRMsymbol shared_root_name) []
  , lookup namespace_map (DRMtype shared_root_name) [] ).
Proof. vm_compute. reflexivity. Qed.

Definition indexed_nested_map : source_map := {|
  files := [];
  origin_data := IndexedOrigins simple_indexed_provenance;
  declarations := nested_map.(declarations)
|}.

Example indexed_lookup_path_and_empty_parity :
  ( lookup indexed_nested_map (DRSymbol shared_root_name) []
  , lookup indexed_nested_map (DRSymbol shared_root_name) [0]
  , lookup indexed_nested_map (DRSymbol shared_root_name) [1; 0]
  , lookup indexed_nested_map (DRSymbol shared_root_name) [1] ) =
  ( lookup nested_map (DRSymbol shared_root_name) []
  , lookup nested_map (DRSymbol shared_root_name) [0]
  , lookup nested_map (DRSymbol shared_root_name) [1; 0]
  , lookup nested_map (DRSymbol shared_root_name) [1] ).
Proof. vm_compute. reflexivity. Qed.

Example indexed_lookup_root_and_child_error_parity :
  ( lookup indexed_nested_map (DRSymbol absent_root_name) []
  , lookup indexed_nested_map (DRSymbol shared_root_name) [2]
  , lookup indexed_nested_map (DRSymbol shared_root_name) [1; 1] ) =
  ( lookup nested_map (DRSymbol absent_root_name) []
  , lookup nested_map (DRSymbol shared_root_name) [2]
  , lookup nested_map (DRSymbol shared_root_name) [1; 1] ).
Proof. vm_compute. reflexivity. Qed.

Definition indexed_invalid_id_map : source_map := {|
  files := [];
  origin_data := IndexedOrigins simple_indexed_provenance;
  declarations := invalid_id_map.(declarations)
|}.

Example indexed_lookup_invalid_origin_parity :
  lookup indexed_invalid_id_map (DRSymbol shared_root_name) [] =
    lookup invalid_id_map (DRSymbol shared_root_name) [].
Proof. vm_compute. reflexivity. Qed.

Definition indexed_ordered_map : source_map := {|
  files := [];
  origin_data := IndexedOrigins simple_indexed_provenance;
  declarations := ordered_multi_origin_map.(declarations)
|}.

Example indexed_lookup_origin_order_parity :
  lookup indexed_ordered_map (DRSymbol shared_root_name) [] =
    lookup ordered_multi_origin_map (DRSymbol shared_root_name) [].
Proof. vm_compute. reflexivity. Qed.

Definition rich_points : list physical_point :=
  [ Build_physical_point 0 1%N 2%N 3%N
  ; Build_physical_point 0 4%N 5%N 6%N
  ; Build_physical_point 0 7%N 8%N 9%N
  ; Build_physical_point 0 10%N 11%N 12%N
  ].

Definition rich_ranges : list Encoded.encoded_range :=
  [ Encoded.EncodedRawRange (Some 0%uint63) None CharacterRange
  ; Encoded.EncodedSameBeginRange 0%uint63 1%uint63 TokenRange 1%uint63
  ; Encoded.EncodedGeneralRange 0%uint63 1%uint63 CharacterRange
      2%uint63 3%uint63
  ].

Definition rich_frame : Encoded.encoded_macro_frame :=
  Encoded.Build_encoded_macro_frame (Some "MACRO"%pstring) MacroArgument
    (Some 0%uint63) (Some 1%uint63).

Definition rich_inline_frame : Encoded.encoded_macro_frame :=
  Encoded.Build_encoded_macro_frame (Some "INLINE"%pstring) MacroBody
    (Some 2%uint63) None.

Definition rich_encoded_origin : Encoded.encoded_origin :=
  Encoded.Build_encoded_origin ExplicitOrigin
    (Some 2%uint63) (Some 1%uint63)
    (Some 0%uint63) (Some 1%uint63)
    [ Encoded.MacroFrameReference 0%uint63
    ; Encoded.InlineMacroFrame rich_inline_frame
    ] (Some 3%uint63) (Some 1) [1].

Definition rich_reference_encoded_origin : Encoded.encoded_origin :=
  Encoded.Build_encoded_origin ImplicitOrigin
    None None None None [] None None [].

Definition rich_indexed_provenance : Encoded.indexed_provenance :=
  Encoded.Build_indexed_provenance
    (indexed_table_of_list Encoded.default_presumed_filename
      ["logical.cpp"%pstring])
    (indexed_table_of_list Encoded.default_physical_point rich_points)
    (indexed_table_of_list Encoded.default_encoded_presumed_point
      [ Encoded.Build_encoded_presumed_point 0%uint63 20%N 21%N
      ; Encoded.Build_encoded_presumed_point 0%uint63 22%N 23%N
      ])
    (indexed_table_of_list Encoded.default_encoded_range rich_ranges)
    (indexed_table_of_list Encoded.default_encoded_macro_frame [rich_frame])
    (indexed_table_of_list Encoded.default_encoded_origin
      [rich_encoded_origin; rich_reference_encoded_origin]).

Definition rich_origin : source_origin :=
  Build_source_origin ExplicitOrigin
    (Some (Build_source_range
      (Some (Build_physical_point 0 1%N 2%N 3%N))
      (Some (Build_physical_point 0 4%N 5%N 6%N)) CharacterRange
      (Some (Build_physical_point 0 7%N 8%N 9%N,
             Build_physical_point 0 10%N 11%N 12%N))))
    (Some (Build_source_range
      (Some (Build_physical_point 0 1%N 2%N 3%N))
      (Some (Build_physical_point 0 4%N 5%N 6%N)) TokenRange
      (Some (Build_physical_point 0 1%N 2%N 3%N,
             Build_physical_point 0 4%N 5%N 6%N))))
    (Some (Build_presumed_point "logical.cpp"%pstring 20%N 21%N))
    (Some (Build_presumed_point "logical.cpp"%pstring 22%N 23%N))
    [ Build_macro_frame (Some "MACRO"%pstring) MacroArgument
        (Some (Build_source_range
          (Some (Build_physical_point 0 1%N 2%N 3%N)) None
          CharacterRange None))
        (Some (Build_source_range
          (Some (Build_physical_point 0 1%N 2%N 3%N))
          (Some (Build_physical_point 0 4%N 5%N 6%N)) TokenRange
          (Some (Build_physical_point 0 1%N 2%N 3%N,
                 Build_physical_point 0 4%N 5%N 6%N))))
    ; Build_macro_frame (Some "INLINE"%pstring) MacroBody
        (Some (Build_source_range
          (Some (Build_physical_point 0 1%N 2%N 3%N))
          (Some (Build_physical_point 0 4%N 5%N 6%N)) CharacterRange
          (Some (Build_physical_point 0 7%N 8%N 9%N,
                 Build_physical_point 0 10%N 11%N 12%N)))) None
    ] (Some (Build_physical_point 0 10%N 11%N 12%N)) (Some 1) [1].

Definition rich_reference_origin : source_origin :=
  test_origin ImplicitOrigin None [].

Definition indexed_leaf_map
    (tables : Encoded.indexed_provenance) (ids : list origin_id)
    : source_map := {|
  files := [];
  origin_data := IndexedOrigins tables;
  declarations := {|
    symbol_locations := <[shared_root_name := leaf ids]> ∅;
    type_locations := ∅;
    msymbol_locations := ∅;
    mtype_locations := ∅
  |}
|}.

Example indexed_lookup_decodes_every_nested_field :
  lookup (indexed_leaf_map rich_indexed_provenance [0])
    (DRSymbol shared_root_name) [] = inr [rich_origin].
Proof. vm_compute. reflexivity. Qed.

Definition rich_expanded_map : source_map := {|
  files := [];
  origin_data := ExpandedOrigins [rich_origin; rich_reference_origin];
  declarations :=
    (indexed_leaf_map rich_indexed_provenance [0]).(declarations)
|}.

Example indexed_rich_lookup_matches_expanded_map :
  lookup (indexed_leaf_map rich_indexed_provenance [0])
    (DRSymbol shared_root_name) [] =
  lookup rich_expanded_map (DRSymbol shared_root_name) [].
Proof. vm_compute. reflexivity. Qed.

Example indexed_diagnostic_materialization_matches_lookup_value :
  Internal.materialize_origins (IndexedOrigins rich_indexed_provenance) =
    inr [rich_origin; rich_reference_origin].
Proof. vm_compute. reflexivity. Qed.

Definition provenance_with_origins
    (tables : Encoded.indexed_provenance)
    (encoded_origins : list Encoded.encoded_origin)
    : Encoded.indexed_provenance :=
  Encoded.Build_indexed_provenance
    tables.(Encoded.presumed_filename_table)
    tables.(Encoded.physical_point_table)
    tables.(Encoded.presumed_point_table)
    tables.(Encoded.range_table)
    tables.(Encoded.macro_frame_table)
    (indexed_table_of_list Encoded.default_encoded_origin encoded_origins).

Definition malformed_range_origin : Encoded.encoded_origin :=
  Encoded.Build_encoded_origin ExplicitOrigin (Some 99%uint63) None
    None None [] None None [].

Definition malformed_anchor_origin : Encoded.encoded_origin :=
  Encoded.Build_encoded_origin ExplicitOrigin (Some 99%uint63) None
    None None [] None (Some 9) [].

Definition malformed_derived_origin : Encoded.encoded_origin :=
  Encoded.Build_encoded_origin ExplicitOrigin None None
    None None [] None None [8; 7].

Example indexed_lookup_reports_private_range_corruption :
  lookup (indexed_leaf_map
      (provenance_with_origins rich_indexed_provenance
        [malformed_range_origin]) [0])
    (DRSymbol shared_root_name) [] =
  inl (MalformedProvenance (DRSymbol shared_root_name) [] 0
    (Encoded.MissingTableEntry Encoded.RangeTable 99%uint63)).
Proof. vm_compute. reflexivity. Qed.

Example indexed_lookup_checks_anchor_before_nested_content :
  lookup (indexed_leaf_map
      (provenance_with_origins rich_indexed_provenance
        [malformed_anchor_origin]) [0])
    (DRSymbol shared_root_name) [] =
  inl (OriginIdOutOfBounds (DRSymbol shared_root_name) [] 9).
Proof. vm_compute. reflexivity. Qed.

Example indexed_lookup_reports_first_invalid_derivation :
  lookup (indexed_leaf_map
      (provenance_with_origins rich_indexed_provenance
        [malformed_derived_origin]) [0])
    (DRSymbol shared_root_name) [] =
  inl (OriginIdOutOfBounds (DRSymbol shared_root_name) [] 8).
Proof. vm_compute. reflexivity. Qed.

Definition unreachable_malformed_provenance : Encoded.indexed_provenance :=
  provenance_with_origins rich_indexed_provenance
    [rich_encoded_origin; malformed_range_origin].

Example indexed_lookup_does_not_decode_unreachable_rows :
  lookup (indexed_leaf_map unreachable_malformed_provenance [0])
    (DRSymbol shared_root_name) [] = inr [rich_origin].
Proof. vm_compute. reflexivity. Qed.

Example indexed_lookup_decodes_only_until_first_failure :
  lookup (indexed_leaf_map unreachable_malformed_provenance [1; 0])
    (DRSymbol shared_root_name) [] =
  inl (MalformedProvenance (DRSymbol shared_root_name) [] 1
    (Encoded.MissingTableEntry Encoded.RangeTable 99%uint63)).
Proof. vm_compute. reflexivity. Qed.

Definition provenance_with_origin_table
    (tables : Encoded.indexed_provenance)
    (encoded_origins : Encoded.indexed_table Encoded.encoded_origin)
    : Encoded.indexed_provenance :=
  Encoded.Build_indexed_provenance
    tables.(Encoded.presumed_filename_table)
    tables.(Encoded.physical_point_table)
    tables.(Encoded.presumed_point_table)
    tables.(Encoded.range_table)
    tables.(Encoded.macro_frame_table) encoded_origins.

Definition missing_outer_origin_table
    : Encoded.indexed_table Encoded.encoded_origin :=
  Encoded.Build_indexed_table 1%uint63
    (PArray.of_list
      (PArray.of_list Encoded.default_encoded_origin []) []).

Definition missing_inner_origin_table
    : Encoded.indexed_table Encoded.encoded_origin :=
  Encoded.Build_indexed_table 1%uint63
    (PArray.of_list (PArray.of_list Encoded.default_encoded_origin [])
      [PArray.of_list Encoded.default_encoded_origin []]).

Example indexed_lookup_distinguishes_missing_outer_storage :
  lookup (indexed_leaf_map
      (provenance_with_origin_table rich_indexed_provenance
        missing_outer_origin_table) [0])
    (DRSymbol shared_root_name) [] =
  inl (MalformedProvenance (DRSymbol shared_root_name) [] 0
    (Encoded.MissingTableEntry Encoded.OriginTable 0%uint63)).
Proof. vm_compute. reflexivity. Qed.

Example indexed_lookup_distinguishes_missing_inner_storage :
  lookup (indexed_leaf_map
      (provenance_with_origin_table rich_indexed_provenance
        missing_inner_origin_table) [0])
    (DRSymbol shared_root_name) [] =
  inl (MalformedProvenance (DRSymbol shared_root_name) [] 0
    (Encoded.MissingTableEntry Encoded.OriginTable 0%uint63)).
Proof. vm_compute. reflexivity. Qed.

Definition storage_missing_anchor_origin : Encoded.encoded_origin :=
  Encoded.Build_encoded_origin InheritedOrigin
    None None None None [] None (Some 1) [].

Definition storage_missing_derived_origin : Encoded.encoded_origin :=
  Encoded.Build_encoded_origin InheritedOrigin
    None None None None [] None None [1].

Definition short_two_origin_table
    (first : Encoded.encoded_origin)
    : Encoded.indexed_table Encoded.encoded_origin :=
  Encoded.Build_indexed_table 2%uint63
    (PArray.of_list (PArray.of_list Encoded.default_encoded_origin [])
      [PArray.of_list Encoded.default_encoded_origin [first]]).

Example indexed_lookup_distinguishes_missing_anchor_storage :
  lookup (indexed_leaf_map
      (provenance_with_origin_table rich_indexed_provenance
        (short_two_origin_table storage_missing_anchor_origin)) [0])
    (DRSymbol shared_root_name) [] =
  inl (MalformedProvenance (DRSymbol shared_root_name) [] 0
    (Encoded.MissingTableEntry Encoded.OriginTable 1%uint63)).
Proof. vm_compute. reflexivity. Qed.

Example indexed_lookup_distinguishes_missing_derivation_storage :
  lookup (indexed_leaf_map
      (provenance_with_origin_table rich_indexed_provenance
        (short_two_origin_table storage_missing_derived_origin)) [0])
    (DRSymbol shared_root_name) [] =
  inl (MalformedProvenance (DRSymbol shared_root_name) [] 0
    (Encoded.MissingTableEntry Encoded.OriginTable 1%uint63)).
Proof. vm_compute. reflexivity. Qed.

Definition boundary_chunk0 : PArray.array nat :=
  PArray.set (PArray.make 4096%uint63 0) 4095%uint63 7.

Definition boundary_table : Encoded.indexed_table nat :=
  Encoded.Build_indexed_table 4097%uint63
    (PArray.of_list (PArray.of_list 0 [])
      [boundary_chunk0; PArray.of_list 0 [8]]).

Example indexed_table_chunk_boundaries :
  ( Encoded.table_get boundary_table 4095%uint63
  , Encoded.table_get boundary_table 4096%uint63
  , Encoded.table_get boundary_table 4097%uint63 ) =
  (Some 7, Some 8, None).
Proof. vm_compute. reflexivity. Qed.

Example indexed_empty_table_is_checked :
  Encoded.table_get (indexed_table_of_list 0 []) 0%uint63 = None.
Proof. vm_compute. reflexivity. Qed.

Definition int_type : type := "int"%cpp_type.
Definition bool_type : type := "bool"%cpp_type.

Definition test_obj_value : ObjValue := Ovar int_type global_init.NoInit.

Definition tactic_constructed_indexed_map : source_map.
Proof.
  Construction.build_indexed_source_map_or_fail ([] : list source_file)
    unreachable_malformed_provenance
    [Construction.LESymbol shared_root_name test_obj_value (leaf [0])].
Defined.

Example indexed_construction_does_not_decode_provenance :
  lookup tactic_constructed_indexed_map (DRSymbol shared_root_name) [] =
    inr [rich_origin].
Proof. vm_compute. reflexivity. Qed.

Example direct_obj_value_insertion_equivalence :
  translation_unit.list_decls
    [Dobj_value shared_root_name test_obj_value] abi.abi_default =
  translation_unit.list_decls
    [Dvariable shared_root_name int_type global_init.NoInit] abi.abi_default.
Proof. vm_compute. reflexivity. Qed.

Example direct_glob_decl_insertion_equivalence :
  translation_unit.list_decls
    [Dglob_decl shared_root_name Gtype] abi.abi_default =
  translation_unit.list_decls
    [Dtype shared_root_name] abi.abi_default.
Proof. vm_compute. reflexivity. Qed.

Definition test_class_name : name := "C"%cpp_name.
Definition static_method_name : name := "C::f()"%cpp_name.
Definition test_static_method : Method := {|
  m_return := int_type;
  m_class := test_class_name;
  m_this_qual := QM;
  m_params := [];
  m_cc := CC_C;
  m_arity := Ar_Definite;
  m_exception := exception_spec.Unknown;
  m_body := None
|}.

Example direct_static_method_final_value_equivalence :
  translation_unit.list_decls
    [Dobj_value static_method_name
      (Ofunction (static_method test_static_method))] abi.abi_default =
  translation_unit.list_decls
    [Dmethod static_method_name true test_static_method] abi.abi_default.
Proof. vm_compute. reflexivity. Qed.

Definition test_enum_name : name := "E"%cpp_name.
Definition test_enumerator_name : name := "E::A"%cpp_name.
Definition test_enumerator_value : GlobDecl :=
  let enum_type := Tenum test_enum_name in
  Gconstant enum_type
    (Some (Ecast (Cintegral enum_type) (Eint 7 int_type))).

Example direct_enum_constant_final_value_equivalence :
  translation_unit.list_decls
    [Dglob_decl test_enumerator_name test_enumerator_value] abi.abi_default =
  translation_unit.list_decls
    [Denum_constant test_enumerator_name test_enum_name int_type
      (inr 7%Z : N + Z) None] abi.abi_default.
Proof. vm_compute. reflexivity. Qed.

Definition test_template_obj : template MObjValue :=
  Template [] test_obj_value.
Definition test_template_glob : template MGlobDecl :=
  Template [] Gtype.
Definition test_template_alias : template Mtype :=
  Template [] int_type.

Example direct_template_obj_insertion_equivalence :
  Mtranslation_unit.decls
    [Dtemplated_obj_value shared_root_name test_template_obj] =
  Mtranslation_unit.decls
    [Dtemplated_variable [] shared_root_name int_type global_init.NoInit].
Proof. vm_compute. reflexivity. Qed.

Example direct_template_glob_insertion_equivalence :
  Mtranslation_unit.decls
    [Dtemplated_glob_decl shared_root_name test_template_glob] =
  Mtranslation_unit.decls
    [Dtemplated_type [] shared_root_name].
Proof. vm_compute. reflexivity. Qed.

Example direct_template_alias_insertion_equivalence :
  Mtranslation_unit.decls
    [Dtemplated_type_alias shared_root_name test_template_alias] =
  Mtranslation_unit.decls
    [Dtemplated_typedef [] shared_root_name int_type].
Proof. vm_compute. reflexivity. Qed.

Example direct_template_enum_constant_final_value_equivalence :
  Mtranslation_unit.decls
    [Dtemplated_glob_decl test_enumerator_name
      (Template [] test_enumerator_value)] =
  Mtranslation_unit.decls
    [Dtemplated_enum_constant [] test_enumerator_name test_enum_name int_type
      (inr 7%Z : N + Z) None].
Proof. vm_compute. reflexivity. Qed.

Definition test_preinst : Mtpreinst :=
  TPreInst shared_root_name [].

Example direct_template_preinst_insertion :
  (Mtranslation_unit.decls
    [Dtemplate_preinst shared_root_name test_preinst]).(templates.minstances)
      !! shared_root_name = Some test_preinst.
Proof. vm_compute. reflexivity. Qed.

Example direct_template_preinst_insertion_equivalence :
  Mtranslation_unit.decls
    [Dtemplate_preinst shared_root_name test_preinst] =
  Mtranslation_unit.decls
    [Dinstantiation shared_root_name shared_root_name []].
Proof. vm_compute. reflexivity. Qed.

Definition nontrivial_instance_name : name := "Vec<int>"%cpp_name.
Definition nontrivial_template_name : Mname := "Vec<$T>"%cpp_name.
Definition nontrivial_template_args : list Mtemp_arg := [Atype int_type].
Definition nontrivial_preinst : Mtpreinst :=
  TPreInst nontrivial_template_name nontrivial_template_args.

Example direct_nontrivial_template_preinst_equivalence :
  Mtranslation_unit.decls
    [Dtemplate_preinst nontrivial_instance_name nontrivial_preinst] =
  Mtranslation_unit.decls
    [Dinstantiation nontrivial_instance_name nontrivial_template_name
      nontrivial_template_args].
Proof. vm_compute. reflexivity. Qed.

Example failed_untemp_produces_no_template_event :
  Mtranslation_unit.decls
    [Dinstantiation nontrivial_template_name nontrivial_template_name
      nontrivial_template_args] =
  Mtranslation_unit.decls [].
Proof. vm_compute. reflexivity. Qed.

Definition event_lookup
    (events : list Construction.located_root_event)
    (root : decl_root) (path : loc_path)
    : Construction.construction_error +
      (lookup_error + list source_origin) :=
  match Construction.build_source_map [] test_origins events with
  | inl err => inl err
  | inr map => inr (lookup map root path)
  end.

Definition event_symbol
    (events : list Construction.located_root_event) (n : name)
    : Construction.construction_error + option ObjValue :=
  match Construction.fold_events_from events Construction.empty_state with
  | inl err => inl err
  | inr state =>
      inr (fst <$> state.(Construction.state_symbols) !! n)
  end.

Definition event_type
    (events : list Construction.located_root_event) (n : name)
    : Construction.construction_error + option GlobDecl :=
  match Construction.fold_events_from events Construction.empty_state with
  | inl err => inl err
  | inr state =>
      inr (fst <$> state.(Construction.state_types) !! n)
  end.

Definition event_msymbol
    (events : list Construction.located_root_event) (n : name)
    : Construction.construction_error + option (template MObjValue) :=
  match Construction.fold_events_from events Construction.empty_state with
  | inl err => inl err
  | inr state =>
      inr (fst <$> state.(Construction.state_msymbols) !! n)
  end.

Definition parsed_symbol
    (declarations : list translation_unit.t) (n : name) : option ObjValue :=
  let '(unit, _) :=
    translation_unit.list_decls declarations abi.abi_default in
  unit.(symbols) !! n.

Definition parsed_type
    (declarations : list translation_unit.t) (n : name) : option GlobDecl :=
  let '(unit, _) :=
    translation_unit.list_decls declarations abi.abi_default in
  unit.(types) !! n.

Definition parsed_msymbol
    (declarations : list Mtranslation_unit.t) (n : name)
    : option (template MObjValue) :=
  (Mtranslation_unit.decls declarations).(templates.msymbols) !! n.

Definition parsed_duplicates
    (declarations : list translation_unit.t) : translation_unit.dup_info :=
  snd (translation_unit.list_decls declarations abi.abi_default).

Definition equal_tree0 : loc_tree origin_id :=
  LocNode [0] [leaf [1]].
Definition equal_tree1 : loc_tree origin_id :=
  LocNode [2] [leaf [3]].

Example fold_equal_duplicates_merges_root_origins :
  event_lookup
    [ Construction.LESymbol shared_root_name test_obj_value equal_tree0
    ; Construction.LESymbol shared_root_name test_obj_value equal_tree1
    ] (DRSymbol shared_root_name) [] = inr (inr [origin2; origin0]).
Proof. vm_compute. reflexivity. Qed.

Example fold_equal_duplicates_merges_child_origins :
  event_lookup
    [ Construction.LESymbol shared_root_name test_obj_value equal_tree0
    ; Construction.LESymbol shared_root_name test_obj_value equal_tree1
    ] (DRSymbol shared_root_name) [0] = inr (inr [origin3; origin1]).
Proof. vm_compute. reflexivity. Qed.

Example fold_equal_duplicate_shape_mismatch_is_error :
  Construction.fold_events
    [ Construction.LESymbol shared_root_name test_obj_value (leaf [0])
    ; Construction.LESymbol shared_root_name test_obj_value equal_tree1
    ] = inl (Construction.TreeShapeMismatch (DRSymbol shared_root_name)).
Proof. vm_compute. reflexivity. Qed.

Definition extern_obj_value : ObjValue := Ovar int_type global_init.Extern.
Definition winning_definition_tree : loc_tree origin_id :=
  LocNode [1] [leaf [2]].
Definition losing_declaration_tree : loc_tree origin_id :=
  LocNode [0] [leaf [3]].

Example fold_compatible_symbol_existing_winner_root :
  event_lookup
    [ Construction.LESymbol shared_root_name extern_obj_value losing_declaration_tree
    ; Construction.LESymbol shared_root_name test_obj_value winning_definition_tree
    ] (DRSymbol shared_root_name) [] = inr (inr [origin1; origin0]).
Proof. vm_compute. reflexivity. Qed.

Example fold_compatible_symbol_existing_winner_keeps_children :
  event_lookup
    [ Construction.LESymbol shared_root_name extern_obj_value losing_declaration_tree
    ; Construction.LESymbol shared_root_name test_obj_value winning_definition_tree
    ] (DRSymbol shared_root_name) [0] = inr (inr [origin2]).
Proof. vm_compute. reflexivity. Qed.

Example fold_compatible_symbol_existing_winner_parser_parity :
  event_symbol
    [ Construction.LESymbol shared_root_name extern_obj_value losing_declaration_tree
    ; Construction.LESymbol shared_root_name test_obj_value winning_definition_tree
    ] shared_root_name =
  inr (parsed_symbol
    [ Dobj_value shared_root_name extern_obj_value
    ; Dobj_value shared_root_name test_obj_value
    ] shared_root_name).
Proof. vm_compute. reflexivity. Qed.

Example fold_compatible_symbol_incoming_winner_root :
  event_lookup
    [ Construction.LESymbol shared_root_name test_obj_value winning_definition_tree
    ; Construction.LESymbol shared_root_name extern_obj_value losing_declaration_tree
    ] (DRSymbol shared_root_name) [] = inr (inr [origin1; origin0]).
Proof. vm_compute. reflexivity. Qed.

Example fold_compatible_symbol_incoming_winner_parser_parity :
  event_symbol
    [ Construction.LESymbol shared_root_name test_obj_value winning_definition_tree
    ; Construction.LESymbol shared_root_name extern_obj_value losing_declaration_tree
    ] shared_root_name =
  inr (parsed_symbol
    [ Dobj_value shared_root_name test_obj_value
    ; Dobj_value shared_root_name extern_obj_value
    ] shared_root_name).
Proof. vm_compute. reflexivity. Qed.

Example fold_incompatible_symbol_is_error :
  Construction.fold_events
    [ Construction.LESymbol shared_root_name test_obj_value (leaf [0])
    ; Construction.LESymbol shared_root_name
        (Ovar bool_type global_init.NoInit) (leaf [1])
    ] = inl (Construction.IncompatibleDuplicates
          [(shared_root_name, inr test_obj_value);
           (shared_root_name, inr (Ovar bool_type global_init.NoInit))]).
Proof. vm_compute. reflexivity. Qed.

Example fold_incompatible_symbol_duplicate_order_parser_parity :
  Construction.fold_events
    [ Construction.LESymbol shared_root_name test_obj_value (leaf [0])
    ; Construction.LESymbol shared_root_name
        (Ovar bool_type global_init.NoInit) (leaf [1])
    ] = inl (Construction.IncompatibleDuplicates
      (parsed_duplicates
        [ Dobj_value shared_root_name test_obj_value
        ; Dobj_value shared_root_name (Ovar bool_type global_init.NoInit)
        ])).
Proof. vm_compute. reflexivity. Qed.

Definition unsupported_glob_decl : GlobDecl :=
  Gunsupported "unsupported"%pstring.

Example fold_compatible_type_existing_winner_root :
  event_lookup
    [ Construction.LEType shared_root_name Gtype (leaf [0])
    ; Construction.LEType shared_root_name unsupported_glob_decl (leaf [1])
    ] (DRType shared_root_name) [] = inr (inr [origin1; origin0]).
Proof. vm_compute. reflexivity. Qed.

Example fold_compatible_type_existing_winner_parser_parity :
  event_type
    [ Construction.LEType shared_root_name Gtype (leaf [0])
    ; Construction.LEType shared_root_name unsupported_glob_decl (leaf [1])
    ] shared_root_name =
  inr (parsed_type
    [ Dglob_decl shared_root_name Gtype
    ; Dglob_decl shared_root_name unsupported_glob_decl
    ] shared_root_name).
Proof. vm_compute. reflexivity. Qed.

Example fold_compatible_type_incoming_winner_root :
  event_lookup
    [ Construction.LEType shared_root_name unsupported_glob_decl (leaf [1])
    ; Construction.LEType shared_root_name Gtype (leaf [0])
    ] (DRType shared_root_name) [] = inr (inr [origin1; origin0]).
Proof. vm_compute. reflexivity. Qed.

Example fold_compatible_type_incoming_winner_parser_parity :
  event_type
    [ Construction.LEType shared_root_name unsupported_glob_decl (leaf [1])
    ; Construction.LEType shared_root_name Gtype (leaf [0])
    ] shared_root_name =
  inr (parsed_type
    [ Dglob_decl shared_root_name unsupported_glob_decl
    ; Dglob_decl shared_root_name Gtype
    ] shared_root_name).
Proof. vm_compute. reflexivity. Qed.

Definition mutually_compatible_enum0 : GlobDecl :=
  Genum int_type ["A"%pstring].
Definition mutually_compatible_enum1 : GlobDecl :=
  Genum int_type ["B"%pstring].

Example fold_mutually_compatible_type_first_order_parser_parity :
  event_type
    [ Construction.LEType shared_root_name mutually_compatible_enum0 (leaf [0])
    ; Construction.LEType shared_root_name mutually_compatible_enum1 (leaf [1])
    ] shared_root_name =
  inr (parsed_type
    [ Dglob_decl shared_root_name mutually_compatible_enum0
    ; Dglob_decl shared_root_name mutually_compatible_enum1
    ] shared_root_name).
Proof. vm_compute. reflexivity. Qed.

Example fold_mutually_compatible_type_first_order_selects_tail :
  event_type
    [ Construction.LEType shared_root_name mutually_compatible_enum0 (leaf [0])
    ; Construction.LEType shared_root_name mutually_compatible_enum1 (leaf [1])
    ] shared_root_name = inr (Some mutually_compatible_enum1).
Proof. vm_compute. reflexivity. Qed.

Example fold_mutually_compatible_type_first_order_selects_tail_tree :
  event_lookup
    [ Construction.LEType shared_root_name mutually_compatible_enum0 (leaf [0])
    ; Construction.LEType shared_root_name mutually_compatible_enum1 (leaf [1])
    ] (DRType shared_root_name) [] = inr (inr [origin1; origin0]).
Proof. vm_compute. reflexivity. Qed.

Example fold_mutually_compatible_type_reverse_order_parser_parity :
  event_type
    [ Construction.LEType shared_root_name mutually_compatible_enum1 (leaf [1])
    ; Construction.LEType shared_root_name mutually_compatible_enum0 (leaf [0])
    ] shared_root_name =
  inr (parsed_type
    [ Dglob_decl shared_root_name mutually_compatible_enum1
    ; Dglob_decl shared_root_name mutually_compatible_enum0
    ] shared_root_name).
Proof. vm_compute. reflexivity. Qed.

Example fold_mutually_compatible_type_reverse_order_selects_tail :
  event_type
    [ Construction.LEType shared_root_name mutually_compatible_enum1 (leaf [1])
    ; Construction.LEType shared_root_name mutually_compatible_enum0 (leaf [0])
    ] shared_root_name = inr (Some mutually_compatible_enum0).
Proof. vm_compute. reflexivity. Qed.

Example fold_mutually_compatible_type_reverse_order_selects_tail_tree :
  event_lookup
    [ Construction.LEType shared_root_name mutually_compatible_enum1 (leaf [1])
    ; Construction.LEType shared_root_name mutually_compatible_enum0 (leaf [0])
    ] (DRType shared_root_name) [] = inr (inr [origin0; origin1]).
Proof. vm_compute. reflexivity. Qed.

Example fold_incompatible_type_is_error :
  Construction.fold_events
    [ Construction.LEType shared_root_name (Gtypedef int_type) (leaf [0])
    ; Construction.LEType shared_root_name (Gtypedef bool_type) (leaf [1])
    ] = inl (Construction.IncompatibleDuplicates
          [(shared_root_name, inl (Gtypedef int_type));
           (shared_root_name, inl (Gtypedef bool_type))]).
Proof. vm_compute. reflexivity. Qed.

Example fold_incompatible_type_duplicate_order_parser_parity :
  Construction.fold_events
    [ Construction.LEType shared_root_name (Gtypedef int_type) (leaf [0])
    ; Construction.LEType shared_root_name (Gtypedef bool_type) (leaf [1])
    ] = inl (Construction.IncompatibleDuplicates
      (parsed_duplicates
        [ Dglob_decl shared_root_name (Gtypedef int_type)
        ; Dglob_decl shared_root_name (Gtypedef bool_type)
        ])).
Proof. vm_compute. reflexivity. Qed.

Example fold_suppresses_self_typedef :
  event_lookup
    [ Construction.LEType shared_root_name
        (Gtypedef (Tnamed shared_root_name)) (leaf [0])
    ] (DRType shared_root_name) [] =
      inr (inl (RootNotFound (DRType shared_root_name))).
Proof. vm_compute. reflexivity. Qed.

Example fold_suppresses_self_enum_typedef :
  event_lookup
    [ Construction.LEType shared_root_name
        (Gtypedef (Tenum shared_root_name)) (leaf [0])
    ] (DRType shared_root_name) [] =
      inr (inl (RootNotFound (DRType shared_root_name))).
Proof. vm_compute. reflexivity. Qed.

Example fold_real_type_followed_by_self_typedef_keeps_real_type :
  event_lookup
    [ Construction.LEType shared_root_name unsupported_glob_decl (leaf [0])
    ; Construction.LEType shared_root_name
        (Gtypedef (Tnamed shared_root_name)) (leaf [1])
    ] (DRType shared_root_name) [] = inr (inr [origin0]).
Proof. vm_compute. reflexivity. Qed.

Example fold_real_type_followed_by_self_typedef_parser_parity :
  event_type
    [ Construction.LEType shared_root_name unsupported_glob_decl (leaf [0])
    ; Construction.LEType shared_root_name
        (Gtypedef (Tnamed shared_root_name)) (leaf [1])
    ] shared_root_name =
  inr (parsed_type
    [ Dglob_decl shared_root_name unsupported_glob_decl
    ; Dglob_decl shared_root_name (Gtypedef (Tnamed shared_root_name))
    ] shared_root_name).
Proof. vm_compute. reflexivity. Qed.

Definition old_template_value : template MObjValue :=
  Template [] test_obj_value.
Definition new_template_value : template MObjValue :=
  Template [] (Ovar bool_type global_init.NoInit).

Example fold_equal_template_duplicates_merge_root_origins :
  event_lookup
    [ Construction.LEMsymbol shared_root_name old_template_value equal_tree0
    ; Construction.LEMsymbol shared_root_name old_template_value equal_tree1
    ] (DRMsymbol shared_root_name) [] = inr (inr [origin0; origin2]).
Proof. vm_compute. reflexivity. Qed.

Example fold_equal_template_duplicates_merge_child_origins :
  event_lookup
    [ Construction.LEMsymbol shared_root_name old_template_value equal_tree0
    ; Construction.LEMsymbol shared_root_name old_template_value equal_tree1
    ] (DRMsymbol shared_root_name) [0] = inr (inr [origin1; origin3]).
Proof. vm_compute. reflexivity. Qed.

Example fold_template_overwrite_selects_later_root :
  event_lookup
    [ Construction.LEMsymbol shared_root_name old_template_value
        losing_declaration_tree
    ; Construction.LEMsymbol shared_root_name new_template_value
        winning_definition_tree
    ] (DRMsymbol shared_root_name) [] = inr (inr [origin1; origin0]).
Proof. vm_compute. reflexivity. Qed.

Example fold_template_overwrite_keeps_only_winner_children :
  event_lookup
    [ Construction.LEMsymbol shared_root_name old_template_value
        losing_declaration_tree
    ; Construction.LEMsymbol shared_root_name new_template_value
        winning_definition_tree
    ] (DRMsymbol shared_root_name) [0] = inr (inr [origin2]).
Proof. vm_compute. reflexivity. Qed.

Example fold_template_overwrite_parser_parity :
  event_msymbol
    [ Construction.LEMsymbol shared_root_name old_template_value
        losing_declaration_tree
    ; Construction.LEMsymbol shared_root_name new_template_value
        winning_definition_tree
    ] shared_root_name =
  inr (parsed_msymbol
    [ Dtemplated_obj_value shared_root_name old_template_value
    ; Dtemplated_obj_value shared_root_name new_template_value
    ] shared_root_name).
Proof. vm_compute. reflexivity. Qed.

Example fold_template_reverse_overwrite_parser_parity :
  event_msymbol
    [ Construction.LEMsymbol shared_root_name new_template_value
        winning_definition_tree
    ; Construction.LEMsymbol shared_root_name old_template_value
        losing_declaration_tree
    ] shared_root_name =
  inr (parsed_msymbol
    [ Dtemplated_obj_value shared_root_name new_template_value
    ; Dtemplated_obj_value shared_root_name old_template_value
    ] shared_root_name).
Proof. vm_compute. reflexivity. Qed.

Example fold_template_type_overwrite_selects_later_root :
  event_lookup
    [ Construction.LEMtype shared_root_name (Template [] Gtype) (leaf [0])
    ; Construction.LEMtype shared_root_name
        (Template [] unsupported_glob_decl) (leaf [1])
    ] (DRMtype shared_root_name) [] = inr (inr [origin1; origin0]).
Proof. vm_compute. reflexivity. Qed.

Definition mixed_order_events : list Construction.located_root_event :=
  [ Construction.LEType shared_root_name mutually_compatible_enum0 (leaf [0])
  ; Construction.LEMsymbol shared_root_name old_template_value (leaf [0])
  ; Construction.LEType shared_root_name mutually_compatible_enum1 (leaf [1])
  ; Construction.LEMsymbol shared_root_name new_template_value (leaf [1])
  ].

Example fold_mixed_events_keep_ordinary_reverse_order :
  event_type mixed_order_events shared_root_name =
    inr (Some mutually_compatible_enum1).
Proof. vm_compute. reflexivity. Qed.

Example fold_mixed_events_keep_template_forward_order :
  event_msymbol mixed_order_events shared_root_name =
    inr (Some new_template_value).
Proof. vm_compute. reflexivity. Qed.
