(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.selection.
Require Import skylabs.lang.cpp.mparser.tu.
Require Import skylabs.lang.cpp.syntax.mcore.
Require Import skylabs.lang.cpp.syntax.source_location.

(** Construction API used by generated source-location companions. [lookup]
    remains the only query operation. *)
Module Construction.
  Inductive located_root_event : Type :=
  | LESymbol
      (name : name) (value : ObjValue) (tree : loc_tree origin_id)
  | LEType
      (name : name) (value : GlobDecl) (tree : loc_tree origin_id)
  | LEMsymbol
      (name : name) (value : template MObjValue) (tree : loc_tree origin_id)
  | LEMtype
      (name : name) (value : template MGlobDecl) (tree : loc_tree origin_id).

  Inductive construction_error : Type :=
  | IncompatibleDuplicates (duplicates : translation_unit.dup_info)
  | TreeShapeMismatch (root : decl_root)
  | InvalidCompactEventClassification (root : decl_root).

  Fixpoint merge_tree {A : Type}
      (existing incoming : loc_tree A) {struct existing}
      : option (loc_tree A) :=
    match existing, incoming with
    | LocNode existing_here existing_children,
      LocNode incoming_here incoming_children =>
        let fix merge_children
            (existing_children : list (loc_tree A))
            (incoming_children : list (loc_tree A))
            : option (list (loc_tree A)) :=
          match existing_children, incoming_children with
          | [], [] => Some []
          | existing_tree :: existing_rest,
            incoming_tree :: incoming_rest =>
              match merge_tree existing_tree incoming_tree,
                    merge_children existing_rest incoming_rest with
              | Some tree, Some rest => Some (tree :: rest)
              | _, _ => None
              end
          | _, _ => None
          end in
        match merge_children existing_children incoming_children with
        | Some children => Some (LocNode (existing_here ++ incoming_here) children)
        | None => None
        end
    end.

  Definition add_losing_root_origins {A : Type}
      (winner loser : loc_tree A) : loc_tree A :=
    match winner, loser with
    | LocNode winner_here winner_children, LocNode loser_here _ =>
        LocNode (winner_here ++ loser_here) winner_children
    end.

  Record state : Type := {
    state_symbols : NM.t (ObjValue * loc_tree origin_id);
    state_types : NM.t (GlobDecl * loc_tree origin_id);
    state_msymbols : TM.t (template MObjValue * loc_tree origin_id);
    state_mtypes : TM.t (template MGlobDecl * loc_tree origin_id)
  }.

  Definition empty_state : state := {|
    state_symbols := ∅;
    state_types := ∅;
    state_msymbols := ∅;
    state_mtypes := ∅
  |}.

  Definition set_symbol
      (n : name) (entry : ObjValue * loc_tree origin_id) (current : state)
      : state := {|
    state_symbols := <[n := entry]> current.(state_symbols);
    state_types := current.(state_types);
    state_msymbols := current.(state_msymbols);
    state_mtypes := current.(state_mtypes)
  |}.

  Definition set_type
      (n : name) (entry : GlobDecl * loc_tree origin_id) (current : state)
      : state := {|
    state_symbols := current.(state_symbols);
    state_types := <[n := entry]> current.(state_types);
    state_msymbols := current.(state_msymbols);
    state_mtypes := current.(state_mtypes)
  |}.

  Definition set_msymbol
      (n : name) (entry : template MObjValue * loc_tree origin_id)
      (current : state) : state := {|
    state_symbols := current.(state_symbols);
    state_types := current.(state_types);
    state_msymbols := <[n := entry]> current.(state_msymbols);
    state_mtypes := current.(state_mtypes)
  |}.

  Definition set_mtype
      (n : name) (entry : template MGlobDecl * loc_tree origin_id)
      (current : state) : state := {|
    state_symbols := current.(state_symbols);
    state_types := current.(state_types);
    state_msymbols := current.(state_msymbols);
    state_mtypes := <[n := entry]> current.(state_mtypes)
  |}.

  Definition add_symbol
      (n : name) (incoming : ObjValue) (incoming_tree : loc_tree origin_id)
      (current : state) : construction_error + state :=
    match current.(state_symbols) !! n with
    | None => inr (set_symbol n (incoming, incoming_tree) current)
    | Some (existing, existing_tree) =>
        if bool_decide (incoming = existing) then
          match merge_tree existing_tree incoming_tree with
          | Some tree => inr (set_symbol n (existing, tree) current)
          | None => inl (TreeShapeMismatch (DRSymbol n))
          end
        else
          match Selection.merge_obj_value incoming existing with
          | None => inl (IncompatibleDuplicates
              [(n, inr incoming); (n, inr existing)])
          | Some winner =>
              if bool_decide (winner = existing) then
                inr (set_symbol n
                  (existing, add_losing_root_origins existing_tree incoming_tree)
                  current)
              else
                inr (set_symbol n
                  (incoming, add_losing_root_origins incoming_tree existing_tree)
                  current)
          end
    end.

  Definition add_type
      (n : name) (incoming : GlobDecl) (incoming_tree : loc_tree origin_id)
      (current : state) : construction_error + state :=
    if Selection.is_self_type_alias n incoming then inr current
    else
      match current.(state_types) !! n with
      | None => inr (set_type n (incoming, incoming_tree) current)
      | Some (existing, existing_tree) =>
          if bool_decide (incoming = existing) then
            match merge_tree existing_tree incoming_tree with
            | Some tree => inr (set_type n (existing, tree) current)
            | None => inl (TreeShapeMismatch (DRType n))
            end
          else
            match Selection.merge_glob_decl incoming existing with
            | None => inl (IncompatibleDuplicates
                [(n, inl incoming); (n, inl existing)])
            | Some winner =>
                if bool_decide (winner = existing) then
                  inr (set_type n
                    (existing, add_losing_root_origins existing_tree incoming_tree)
                    current)
                else
                  inr (set_type n
                    (incoming, add_losing_root_origins incoming_tree existing_tree)
                    current)
            end
      end.

  (** Template tables retain their normal last-write-wins semantics. For an
      unequal overwrite, the later event's tree wins and the overwritten root
      origins are appended only at that root. Equal values with equal shape
      merge recursively, like ordinary equal declarations. *)
  Definition add_msymbol
      (n : name) (incoming : template MObjValue)
      (incoming_tree : loc_tree origin_id) (current : state)
      : construction_error + state :=
    match current.(state_msymbols) !! n with
    | None => inr (set_msymbol n (incoming, incoming_tree) current)
    | Some (existing, existing_tree) =>
        if bool_decide (incoming = existing) then
          match merge_tree existing_tree incoming_tree with
          | Some tree => inr (set_msymbol n (existing, tree) current)
          | None => inl (TreeShapeMismatch (DRMsymbol n))
          end
        else
          inr (set_msymbol n
            (incoming, add_losing_root_origins incoming_tree existing_tree)
            current)
    end.

  Definition add_mtype
      (n : name) (incoming : template MGlobDecl)
      (incoming_tree : loc_tree origin_id) (current : state)
      : construction_error + state :=
    match current.(state_mtypes) !! n with
    | None => inr (set_mtype n (incoming, incoming_tree) current)
    | Some (existing, existing_tree) =>
        if bool_decide (incoming = existing) then
          match merge_tree existing_tree incoming_tree with
          | Some tree => inr (set_mtype n (existing, tree) current)
          | None => inl (TreeShapeMismatch (DRMtype n))
          end
        else
          inr (set_mtype n
            (incoming, add_losing_root_origins incoming_tree existing_tree)
            current)
    end.

  (** [translation_unit.array_fold] composes ordinary declarations from the
      end of its [PArray] toward the beginning, while
      [Mtranslation_unit.decls'] processes template declarations head-to-tail.
      The four tables are independent, so mixed event kinds can follow their
      table-specific order without introducing cross-table ordering. *)
  Fixpoint fold_events_from
      (events : list located_root_event) (current : state)
      : construction_error + state :=
    match events with
    | [] => inr current
    | LESymbol n value tree :: rest =>
        match fold_events_from rest current with
        | inl err => inl err
        | inr next => add_symbol n value tree next
        end
    | LEType n value tree :: rest =>
        match fold_events_from rest current with
        | inl err => inl err
        | inr next => add_type n value tree next
        end
    | LEMsymbol n value tree :: rest =>
        match add_msymbol n value tree current with
        | inl err => inl err
        | inr next => fold_events_from rest next
        end
    | LEMtype n value tree :: rest =>
        match add_mtype n value tree current with
        | inl err => inl err
        | inr next => fold_events_from rest next
        end
    end.

  Definition project_locations (current : state)
      : declaration_locations origin_id := {|
    symbol_locations := NM.map snd current.(state_symbols);
    type_locations := NM.map snd current.(state_types);
    msymbol_locations := TM.map snd current.(state_msymbols);
    mtype_locations := TM.map snd current.(state_mtypes)
  |}.

  Definition fold_events (events : list located_root_event)
      : construction_error + declaration_locations origin_id :=
    match fold_events_from events empty_state with
    | inl err => inl err
    | inr current => inr (project_locations current)
    end.

  Definition assemble_source_map
      (source_files : list source_file) (source_origins : origin_store)
      (locations : declaration_locations origin_id) : source_map := {|
    files := source_files;
    origin_data := source_origins;
    location_data := ExpandedLocations locations
  |}.

  Definition build_source_map
      (source_files : list source_file) (source_origins : list source_origin)
      (events : list located_root_event)
      : construction_error + source_map :=
    match fold_events events with
    | inl err => inl err
    | inr locations =>
        inr (assemble_source_map source_files
          (ExpandedOrigins source_origins) locations)
    end.

  Definition build_indexed_source_map
      (source_files : list source_file)
      (source_origins : Encoded.indexed_provenance)
      (events : list located_root_event)
      : construction_error + source_map :=
    match fold_events events with
    | inl err => inl err
    | inr locations =>
        inr (assemble_source_map source_files
          (IndexedOrigins source_origins) locations)
    end.

  (** Only root-event selection is reduced. Provenance is deliberately absent
      from the evaluated term, so construction cannot decode an indexed table. *)
  Ltac build_source_map_or_fail source_files source_origins events :=
    let result := eval vm_compute in (fold_events events) in
    lazymatch result with
    | inr ?locations =>
        exact (assemble_source_map source_files
          (ExpandedOrigins source_origins) locations)
    | inl ?error => fail "source-location construction failed:" error
    end.

  Ltac build_indexed_source_map_or_fail source_files source_origins events :=
    let result := eval vm_compute in (fold_events events) in
    lazymatch result with
    | inr ?locations =>
        exact (assemble_source_map source_files
          (IndexedOrigins source_origins) locations)
    | inl ?error => fail "source-location construction failed:" error
    end.

  (** Compact events carry only static location-node and exact-shape IDs.
      Semantic selection remains in Rocq, while duplicate composition builds
      lazy views and never reads or expands the location DAG. *)
  Inductive indexed_located_root_event : Type :=
  | ILESymbol
      (name : name) (value : ObjValue)
      (node shape : Encoded.table_id)
  | ILEType
      (name : name) (value : GlobDecl)
      (node shape : Encoded.table_id)
  | ILEMsymbol
      (name : name) (value : template MObjValue)
      (node shape : Encoded.table_id)
  | ILEMtype
      (name : name) (value : template MGlobDecl)
      (node shape : Encoded.table_id).

  Definition merge_indexed_location
      (existing incoming : indexed_location) : option indexed_location :=
    let existing_shape := indexed_location_shape existing in
    let incoming_shape := indexed_location_shape incoming in
    if PrimInt63.eqb existing_shape incoming_shape then
      Some (MergeLocations existing_shape existing incoming)
    else None.

  Definition add_losing_indexed_root
      (winner loser : indexed_location) : indexed_location :=
    AddRootOrigins (indexed_location_shape winner) winner loser.

  Record indexed_state : Type := {
    indexed_state_symbols : NM.t (ObjValue * indexed_location);
    indexed_state_types : NM.t (GlobDecl * indexed_location);
    indexed_state_msymbols : TM.t (template MObjValue * indexed_location);
    indexed_state_mtypes : TM.t (template MGlobDecl * indexed_location)
  }.

  Definition empty_indexed_state : indexed_state := {|
    indexed_state_symbols := ∅;
    indexed_state_types := ∅;
    indexed_state_msymbols := ∅;
    indexed_state_mtypes := ∅
  |}.

  Definition set_indexed_symbol
      (n : name) (entry : ObjValue * indexed_location)
      (current : indexed_state) : indexed_state := {|
    indexed_state_symbols := <[n := entry]> current.(indexed_state_symbols);
    indexed_state_types := current.(indexed_state_types);
    indexed_state_msymbols := current.(indexed_state_msymbols);
    indexed_state_mtypes := current.(indexed_state_mtypes)
  |}.

  Definition set_indexed_type
      (n : name) (entry : GlobDecl * indexed_location)
      (current : indexed_state) : indexed_state := {|
    indexed_state_symbols := current.(indexed_state_symbols);
    indexed_state_types := <[n := entry]> current.(indexed_state_types);
    indexed_state_msymbols := current.(indexed_state_msymbols);
    indexed_state_mtypes := current.(indexed_state_mtypes)
  |}.

  Definition set_indexed_msymbol
      (n : name) (entry : template MObjValue * indexed_location)
      (current : indexed_state) : indexed_state := {|
    indexed_state_symbols := current.(indexed_state_symbols);
    indexed_state_types := current.(indexed_state_types);
    indexed_state_msymbols :=
      <[n := entry]> current.(indexed_state_msymbols);
    indexed_state_mtypes := current.(indexed_state_mtypes)
  |}.

  Definition set_indexed_mtype
      (n : name) (entry : template MGlobDecl * indexed_location)
      (current : indexed_state) : indexed_state := {|
    indexed_state_symbols := current.(indexed_state_symbols);
    indexed_state_types := current.(indexed_state_types);
    indexed_state_msymbols := current.(indexed_state_msymbols);
    indexed_state_mtypes := <[n := entry]> current.(indexed_state_mtypes)
  |}.

  Definition add_indexed_symbol
      (n : name) (incoming : ObjValue)
      (incoming_location : indexed_location) (current : indexed_state)
      : construction_error + indexed_state :=
    match current.(indexed_state_symbols) !! n with
    | None =>
        inr (set_indexed_symbol n (incoming, incoming_location) current)
    | Some (existing, existing_location) =>
        if bool_decide (incoming = existing) then
          match merge_indexed_location existing_location incoming_location with
          | Some location =>
              inr (set_indexed_symbol n (existing, location) current)
          | None => inl (TreeShapeMismatch (DRSymbol n))
          end
        else
          match Selection.merge_obj_value incoming existing with
          | None => inl (IncompatibleDuplicates
              [(n, inr incoming); (n, inr existing)])
          | Some winner =>
              if bool_decide (winner = existing) then
                inr (set_indexed_symbol n
                  (existing, add_losing_indexed_root
                    existing_location incoming_location) current)
              else
                inr (set_indexed_symbol n
                  (incoming, add_losing_indexed_root
                    incoming_location existing_location) current)
          end
    end.

  Definition add_indexed_type
      (n : name) (incoming : GlobDecl)
      (incoming_location : indexed_location) (current : indexed_state)
      : construction_error + indexed_state :=
    if Selection.is_self_type_alias n incoming then inr current
    else
      match current.(indexed_state_types) !! n with
      | None => inr (set_indexed_type n (incoming, incoming_location) current)
      | Some (existing, existing_location) =>
          if bool_decide (incoming = existing) then
            match merge_indexed_location existing_location incoming_location with
            | Some location =>
                inr (set_indexed_type n (existing, location) current)
            | None => inl (TreeShapeMismatch (DRType n))
            end
          else
            match Selection.merge_glob_decl incoming existing with
            | None => inl (IncompatibleDuplicates
                [(n, inl incoming); (n, inl existing)])
            | Some winner =>
                if bool_decide (winner = existing) then
                  inr (set_indexed_type n
                    (existing, add_losing_indexed_root
                      existing_location incoming_location) current)
                else
                  inr (set_indexed_type n
                    (incoming, add_losing_indexed_root
                      incoming_location existing_location) current)
            end
      end.

  Definition add_indexed_msymbol
      (n : name) (incoming : template MObjValue)
      (incoming_location : indexed_location) (current : indexed_state)
      : construction_error + indexed_state :=
    match current.(indexed_state_msymbols) !! n with
    | None =>
        inr (set_indexed_msymbol n (incoming, incoming_location) current)
    | Some (existing, existing_location) =>
        if bool_decide (incoming = existing) then
          match merge_indexed_location existing_location incoming_location with
          | Some location =>
              inr (set_indexed_msymbol n (existing, location) current)
          | None => inl (TreeShapeMismatch (DRMsymbol n))
          end
        else
          inr (set_indexed_msymbol n
            (incoming, add_losing_indexed_root
              incoming_location existing_location) current)
    end.

  Definition add_indexed_mtype
      (n : name) (incoming : template MGlobDecl)
      (incoming_location : indexed_location) (current : indexed_state)
      : construction_error + indexed_state :=
    match current.(indexed_state_mtypes) !! n with
    | None => inr (set_indexed_mtype n (incoming, incoming_location) current)
    | Some (existing, existing_location) =>
        if bool_decide (incoming = existing) then
          match merge_indexed_location existing_location incoming_location with
          | Some location =>
              inr (set_indexed_mtype n (existing, location) current)
          | None => inl (TreeShapeMismatch (DRMtype n))
          end
        else
          inr (set_indexed_mtype n
            (incoming, add_losing_indexed_root
              incoming_location existing_location) current)
    end.

  Fixpoint fold_indexed_events_from
      (events : list indexed_located_root_event) (current : indexed_state)
      : construction_error + indexed_state :=
    match events with
    | [] => inr current
    | ILESymbol n value node shape :: rest =>
        match fold_indexed_events_from rest current with
        | inl error => inl error
        | inr next => add_indexed_symbol n value
            (StaticLocation node shape) next
        end
    | ILEType n value node shape :: rest =>
        match fold_indexed_events_from rest current with
        | inl error => inl error
        | inr next => add_indexed_type n value
            (StaticLocation node shape) next
        end
    | ILEMsymbol n value node shape :: rest =>
        match add_indexed_msymbol n value
            (StaticLocation node shape) current with
        | inl error => inl error
        | inr next => fold_indexed_events_from rest next
        end
    | ILEMtype n value node shape :: rest =>
        match add_indexed_mtype n value
            (StaticLocation node shape) current with
        | inl error => inl error
        | inr next => fold_indexed_events_from rest next
        end
    end.

  Definition project_indexed_locations (current : indexed_state)
      : root_locations indexed_location := {|
    symbol_locations := NM.map snd current.(indexed_state_symbols);
    type_locations := NM.map snd current.(indexed_state_types);
    msymbol_locations := TM.map snd current.(indexed_state_msymbols);
    mtype_locations := TM.map snd current.(indexed_state_mtypes)
  |}.

  Definition fold_indexed_events (events : list indexed_located_root_event)
      : construction_error + root_locations indexed_location :=
    match fold_indexed_events_from events empty_indexed_state with
    | inl error => inl error
    | inr current => inr (project_indexed_locations current)
    end.

  Definition assemble_indexed_dag_source_map
      (source_files : list source_file)
      (source_origins : Encoded.indexed_provenance)
      (dag : Encoded.indexed_location_dag)
      (locations : root_locations indexed_location) : source_map := {|
    files := source_files;
    origin_data := IndexedOrigins source_origins;
    location_data := IndexedLocations dag locations
  |}.

  Definition build_indexed_dag_source_map
      (source_files : list source_file)
      (source_origins : Encoded.indexed_provenance)
      (dag : Encoded.indexed_location_dag)
      (events : list indexed_located_root_event)
      : construction_error + source_map :=
    match fold_indexed_events events with
    | inl error => inl error
    | inr locations => inr (assemble_indexed_dag_source_map
        source_files source_origins dag locations)
    end.

  (** VM computation sees only semantic values, static primitive IDs, and lazy
      composition views. The provenance and DAG tables are supplied after the
      fold result and therefore cannot be decoded or expanded by construction. *)
  Ltac build_indexed_dag_source_map_or_fail
      source_files source_origins dag events :=
    let result := eval vm_compute in (fold_indexed_events events) in
    lazymatch result with
    | inr ?locations =>
        exact (assemble_indexed_dag_source_map
          source_files source_origins dag locations)
    | inl ?error => fail "source-location construction failed:" error
    end.

  (** Proposal-4 events omit semantic values for keys which the producer has
      proved singleton in their root namespace. Residual events retain the
      existing semantic event shape and continue through the authoritative
      selection functions above. *)
  Inductive compact_indexed_located_root_event : Type :=
  | CILESingletonSymbol
      (name : name) (node shape : Encoded.table_id)
  | CILESingletonType
      (name : name) (node shape : Encoded.table_id)
  | CILESingletonMsymbol
      (name : name) (node shape : Encoded.table_id)
  | CILESingletonMtype
      (name : name) (node shape : Encoded.table_id)
  | CILEResidualSymbol
      (name : name) (value : ObjValue)
      (node shape : Encoded.table_id)
  | CILEResidualType
      (name : name) (value : GlobDecl)
      (node shape : Encoded.table_id)
  | CILEResidualMsymbol
      (name : name) (value : template MObjValue)
      (node shape : Encoded.table_id)
  | CILEResidualMtype
      (name : name) (value : template MGlobDecl)
      (node shape : Encoded.table_id).

  (** Classification markers are independent of semantic selection. Each
      namespace stores singleton locations directly, plus a small residual-key
      map. A residual self-type alias therefore remains marked even though
      [add_indexed_type] suppresses it from the selected state. This layout
      avoids rebuilding a second full singleton map during projection. *)
  Record compact_indexed_state : Type := {
    compact_state_symbols : NM.t indexed_location * NM.t unit;
    compact_state_types : NM.t indexed_location * NM.t unit;
    compact_state_msymbols : TM.t indexed_location * TM.t unit;
    compact_state_mtypes : TM.t indexed_location * TM.t unit;
    compact_state_residual : indexed_state
  }.

  Definition empty_compact_indexed_state : compact_indexed_state := {|
    compact_state_symbols := (∅, ∅);
    compact_state_types := (∅, ∅);
    compact_state_msymbols := (∅, ∅);
    compact_state_mtypes := (∅, ∅);
    compact_state_residual := empty_indexed_state
  |}.

  Definition set_compact_symbols
      (entries : NM.t indexed_location * NM.t unit)
      (current : compact_indexed_state) : compact_indexed_state := {|
    compact_state_symbols := entries;
    compact_state_types := current.(compact_state_types);
    compact_state_msymbols := current.(compact_state_msymbols);
    compact_state_mtypes := current.(compact_state_mtypes);
    compact_state_residual := current.(compact_state_residual)
  |}.

  Definition set_compact_types
      (entries : NM.t indexed_location * NM.t unit)
      (current : compact_indexed_state) : compact_indexed_state := {|
    compact_state_symbols := current.(compact_state_symbols);
    compact_state_types := entries;
    compact_state_msymbols := current.(compact_state_msymbols);
    compact_state_mtypes := current.(compact_state_mtypes);
    compact_state_residual := current.(compact_state_residual)
  |}.

  Definition set_compact_msymbols
      (entries : TM.t indexed_location * TM.t unit)
      (current : compact_indexed_state) : compact_indexed_state := {|
    compact_state_symbols := current.(compact_state_symbols);
    compact_state_types := current.(compact_state_types);
    compact_state_msymbols := entries;
    compact_state_mtypes := current.(compact_state_mtypes);
    compact_state_residual := current.(compact_state_residual)
  |}.

  Definition set_compact_mtypes
      (entries : TM.t indexed_location * TM.t unit)
      (current : compact_indexed_state) : compact_indexed_state := {|
    compact_state_symbols := current.(compact_state_symbols);
    compact_state_types := current.(compact_state_types);
    compact_state_msymbols := current.(compact_state_msymbols);
    compact_state_mtypes := entries;
    compact_state_residual := current.(compact_state_residual)
  |}.

  Definition set_compact_residual
      (residual : indexed_state) (current : compact_indexed_state)
      : compact_indexed_state := {|
    compact_state_symbols := current.(compact_state_symbols);
    compact_state_types := current.(compact_state_types);
    compact_state_msymbols := current.(compact_state_msymbols);
    compact_state_mtypes := current.(compact_state_mtypes);
    compact_state_residual := residual
  |}.

  Definition add_compact_singleton_symbol
      (n : name) (node shape : Encoded.table_id)
      (current : compact_indexed_state)
      : construction_error + compact_indexed_state :=
    let '(singletons, residuals) := current.(compact_state_symbols) in
    match singletons !! n, residuals !! n with
    | None, None => inr (set_compact_symbols
        (<[n := StaticLocation node shape]> singletons, residuals) current)
    | _, _ => inl (InvalidCompactEventClassification (DRSymbol n))
    end.

  Definition add_compact_singleton_type
      (n : name) (node shape : Encoded.table_id)
      (current : compact_indexed_state)
      : construction_error + compact_indexed_state :=
    let '(singletons, residuals) := current.(compact_state_types) in
    match singletons !! n, residuals !! n with
    | None, None => inr (set_compact_types
        (<[n := StaticLocation node shape]> singletons, residuals) current)
    | _, _ => inl (InvalidCompactEventClassification (DRType n))
    end.

  Definition add_compact_singleton_msymbol
      (n : name) (node shape : Encoded.table_id)
      (current : compact_indexed_state)
      : construction_error + compact_indexed_state :=
    let '(singletons, residuals) := current.(compact_state_msymbols) in
    match singletons !! n, residuals !! n with
    | None, None => inr (set_compact_msymbols
        (<[n := StaticLocation node shape]> singletons, residuals) current)
    | _, _ => inl (InvalidCompactEventClassification (DRMsymbol n))
    end.

  Definition add_compact_singleton_mtype
      (n : name) (node shape : Encoded.table_id)
      (current : compact_indexed_state)
      : construction_error + compact_indexed_state :=
    let '(singletons, residuals) := current.(compact_state_mtypes) in
    match singletons !! n, residuals !! n with
    | None, None => inr (set_compact_mtypes
        (<[n := StaticLocation node shape]> singletons, residuals) current)
    | _, _ => inl (InvalidCompactEventClassification (DRMtype n))
    end.

  Definition add_compact_residual_symbol
      (n : name) (value : ObjValue) (node shape : Encoded.table_id)
      (current : compact_indexed_state)
      : construction_error + compact_indexed_state :=
    let '(singletons, residuals) := current.(compact_state_symbols) in
    match singletons !! n with
    | Some _ => inl (InvalidCompactEventClassification (DRSymbol n))
    | None =>
        let marked := set_compact_symbols
          (singletons, <[n := tt]> residuals) current in
        match add_indexed_symbol n value (StaticLocation node shape)
            marked.(compact_state_residual) with
        | inl error => inl error
        | inr residual => inr (set_compact_residual residual marked)
        end
    end.

  Definition add_compact_residual_type
      (n : name) (value : GlobDecl) (node shape : Encoded.table_id)
      (current : compact_indexed_state)
      : construction_error + compact_indexed_state :=
    let '(singletons, residuals) := current.(compact_state_types) in
    match singletons !! n with
    | Some _ => inl (InvalidCompactEventClassification (DRType n))
    | None =>
        let marked := set_compact_types
          (singletons, <[n := tt]> residuals) current in
        match add_indexed_type n value (StaticLocation node shape)
            marked.(compact_state_residual) with
        | inl error => inl error
        | inr residual => inr (set_compact_residual residual marked)
        end
    end.

  Definition add_compact_residual_msymbol
      (n : name) (value : template MObjValue)
      (node shape : Encoded.table_id) (current : compact_indexed_state)
      : construction_error + compact_indexed_state :=
    let '(singletons, residuals) := current.(compact_state_msymbols) in
    match singletons !! n with
    | Some _ => inl (InvalidCompactEventClassification (DRMsymbol n))
    | None =>
        let marked := set_compact_msymbols
          (singletons, <[n := tt]> residuals) current in
        match add_indexed_msymbol n value (StaticLocation node shape)
            marked.(compact_state_residual) with
        | inl error => inl error
        | inr residual => inr (set_compact_residual residual marked)
        end
    end.

  Definition add_compact_residual_mtype
      (n : name) (value : template MGlobDecl)
      (node shape : Encoded.table_id) (current : compact_indexed_state)
      : construction_error + compact_indexed_state :=
    let '(singletons, residuals) := current.(compact_state_mtypes) in
    match singletons !! n with
    | Some _ => inl (InvalidCompactEventClassification (DRMtype n))
    | None =>
        let marked := set_compact_mtypes
          (singletons, <[n := tt]> residuals) current in
        match add_indexed_mtype n value (StaticLocation node shape)
            marked.(compact_state_residual) with
        | inl error => inl error
        | inr residual => inr (set_compact_residual residual marked)
        end
    end.

  (** Ordinary tables retain their right-to-left fold. Template tables retain
      their left-to-right fold. Marker registration occurs before semantic
      selection at the current event, so even a suppressed residual alias is
      visible to later classification checks. *)
  Fixpoint fold_compact_indexed_events_from
      (events : list compact_indexed_located_root_event)
      (current : compact_indexed_state)
      : construction_error + compact_indexed_state :=
    match events with
    | [] => inr current
    | CILESingletonSymbol n node shape :: rest =>
        match fold_compact_indexed_events_from rest current with
        | inl error => inl error
        | inr next => add_compact_singleton_symbol n node shape next
        end
    | CILESingletonType n node shape :: rest =>
        match fold_compact_indexed_events_from rest current with
        | inl error => inl error
        | inr next => add_compact_singleton_type n node shape next
        end
    | CILESingletonMsymbol n node shape :: rest =>
        match add_compact_singleton_msymbol n node shape current with
        | inl error => inl error
        | inr next => fold_compact_indexed_events_from rest next
        end
    | CILESingletonMtype n node shape :: rest =>
        match add_compact_singleton_mtype n node shape current with
        | inl error => inl error
        | inr next => fold_compact_indexed_events_from rest next
        end
    | CILEResidualSymbol n value node shape :: rest =>
        match fold_compact_indexed_events_from rest current with
        | inl error => inl error
        | inr next => add_compact_residual_symbol n value node shape next
        end
    | CILEResidualType n value node shape :: rest =>
        match fold_compact_indexed_events_from rest current with
        | inl error => inl error
        | inr next => add_compact_residual_type n value node shape next
        end
    | CILEResidualMsymbol n value node shape :: rest =>
        match add_compact_residual_msymbol n value node shape current with
        | inl error => inl error
        | inr next => fold_compact_indexed_events_from rest next
        end
    | CILEResidualMtype n value node shape :: rest =>
        match add_compact_residual_mtype n value node shape current with
        | inl error => inl error
        | inr next => fold_compact_indexed_events_from rest next
        end
    end.

  Definition residual_left_nm {A : Type}
      (residual singleton : NM.t A) : NM.t A :=
    NM.fold (fun n entry current => <[n := entry]> current)
      residual singleton.

  Definition residual_left_tm {A : Type}
      (residual singleton : TM.t A) : TM.t A :=
    TM.fold (fun n entry current => <[n := entry]> current)
      residual singleton.

  Definition project_compact_indexed_locations
      (current : compact_indexed_state)
      : root_locations indexed_location :=
    let residual := project_indexed_locations current.(compact_state_residual) in
    {|
      symbol_locations := residual_left_nm residual.(symbol_locations)
        (fst current.(compact_state_symbols));
      type_locations := residual_left_nm residual.(type_locations)
        (fst current.(compact_state_types));
      msymbol_locations := residual_left_tm residual.(msymbol_locations)
        (fst current.(compact_state_msymbols));
      mtype_locations := residual_left_tm residual.(mtype_locations)
        (fst current.(compact_state_mtypes))
    |}.

  Definition fold_compact_indexed_events
      (events : list compact_indexed_located_root_event)
      : construction_error + root_locations indexed_location :=
    match fold_compact_indexed_events_from events empty_compact_indexed_state with
    | inl error => inl error
    | inr current => inr (project_compact_indexed_locations current)
    end.

  Definition build_compact_indexed_dag_source_map
      (source_files : list source_file)
      (source_origins : Encoded.indexed_provenance)
      (dag : Encoded.indexed_location_dag)
      (events : list compact_indexed_located_root_event)
      : construction_error + source_map :=
    match fold_compact_indexed_events events with
    | inl error => inl error
    | inr locations => inr (assemble_indexed_dag_source_map
        source_files source_origins dag locations)
    end.

  (** VM computation sees root names, residual semantic values, primitive IDs,
      and compact marker maps only. Provenance and the DAG remain outside the
      evaluated term. *)
  Ltac build_compact_indexed_dag_source_map_or_fail
      source_files source_origins dag events :=
    let result := eval vm_compute in (fold_compact_indexed_events events) in
    lazymatch result with
    | inr ?locations =>
        exact (assemble_indexed_dag_source_map
          source_files source_origins dag locations)
    | inl ?error => fail "source-location construction failed:" error
    end.

  (** Board-scale production construction keeps singleton roots lazy and
      VM-reduces only the small residual semantic groups. The producer's exact
      classifier establishes singleton uniqueness; public lookup independently
      diagnoses malformed duplicate or mixed private storage.

      Filtered companions retain an exact semantic fold while carrying only
      the two bits needed to decide whether its final selected location is
      observable.  This deliberately mirrors the existing selection helpers:
      the ordinary/template fold directions and all incompatibility/self-alias
      decisions remain authoritative above. *)
  Record indexed_location_presence : Type := {
    indexed_presence_at_root : bool;
    indexed_presence_in_tree : bool
  }.

  Definition merge_indexed_presence
      (existing incoming : indexed_location_presence)
      : indexed_location_presence := {|
    indexed_presence_at_root := existing.(indexed_presence_at_root) ||
      incoming.(indexed_presence_at_root);
    indexed_presence_in_tree := existing.(indexed_presence_in_tree) ||
      incoming.(indexed_presence_in_tree)
  |}.

  Definition add_losing_indexed_presence
      (winner loser : indexed_location_presence)
      : indexed_location_presence := {|
    indexed_presence_at_root := winner.(indexed_presence_at_root) ||
      loser.(indexed_presence_at_root);
    indexed_presence_in_tree := winner.(indexed_presence_in_tree) ||
      loser.(indexed_presence_at_root)
  |}.

  Inductive filtered_indexed_located_root_event : Type :=
  | FILESymbol (name : name) (value : ObjValue) (node shape : Encoded.table_id)
      (at_root in_tree : bool)
  | FILEType (name : name) (value : GlobDecl) (node shape : Encoded.table_id)
      (at_root in_tree : bool)
  | FILEMsymbol (name : name) (value : template MObjValue)
      (node shape : Encoded.table_id) (at_root in_tree : bool)
  | FILEMtype (name : name) (value : template MGlobDecl)
      (node shape : Encoded.table_id) (at_root in_tree : bool).

  Definition filtered_event_indexed
      (event : filtered_indexed_located_root_event) : indexed_located_root_event :=
    match event with
    | FILESymbol n value node shape _ _ => ILESymbol n value node shape
    | FILEType n value node shape _ _ => ILEType n value node shape
    | FILEMsymbol n value node shape _ _ => ILEMsymbol n value node shape
    | FILEMtype n value node shape _ _ => ILEMtype n value node shape
    end.

  Record filtered_indexed_state : Type := {
    filtered_symbols : NM.t (ObjValue * indexed_location_presence);
    filtered_types : NM.t (GlobDecl * indexed_location_presence);
    filtered_msymbols : TM.t (template MObjValue * indexed_location_presence);
    filtered_mtypes : TM.t (template MGlobDecl * indexed_location_presence)
  }.

  Definition empty_filtered_indexed_state : filtered_indexed_state := {|
    filtered_symbols := ∅; filtered_types := ∅;
    filtered_msymbols := ∅; filtered_mtypes := ∅
  |}.

  Definition set_filtered_symbol (n : name)
      (entry : ObjValue * indexed_location_presence)
      (current : filtered_indexed_state) : filtered_indexed_state := {|
    filtered_symbols := <[n := entry]> current.(filtered_symbols);
    filtered_types := current.(filtered_types);
    filtered_msymbols := current.(filtered_msymbols);
    filtered_mtypes := current.(filtered_mtypes)
  |}.
  Definition set_filtered_type (n : name)
      (entry : GlobDecl * indexed_location_presence)
      (current : filtered_indexed_state) : filtered_indexed_state := {|
    filtered_symbols := current.(filtered_symbols);
    filtered_types := <[n := entry]> current.(filtered_types);
    filtered_msymbols := current.(filtered_msymbols);
    filtered_mtypes := current.(filtered_mtypes)
  |}.
  Definition set_filtered_msymbol (n : name)
      (entry : template MObjValue * indexed_location_presence)
      (current : filtered_indexed_state) : filtered_indexed_state := {|
    filtered_symbols := current.(filtered_symbols);
    filtered_types := current.(filtered_types);
    filtered_msymbols := <[n := entry]> current.(filtered_msymbols);
    filtered_mtypes := current.(filtered_mtypes)
  |}.
  Definition set_filtered_mtype (n : name)
      (entry : template MGlobDecl * indexed_location_presence)
      (current : filtered_indexed_state) : filtered_indexed_state := {|
    filtered_symbols := current.(filtered_symbols);
    filtered_types := current.(filtered_types);
    filtered_msymbols := current.(filtered_msymbols);
    filtered_mtypes := <[n := entry]> current.(filtered_mtypes)
  |}.

  Definition add_filtered_symbol (n : name) (incoming : ObjValue)
      (presence : indexed_location_presence) (current : filtered_indexed_state)
      : construction_error + filtered_indexed_state :=
    match current.(filtered_symbols) !! n with
    | None => inr (set_filtered_symbol n (incoming, presence) current)
    | Some (existing, existing_presence) =>
        if bool_decide (incoming = existing) then
          inr (set_filtered_symbol n (existing,
            merge_indexed_presence existing_presence presence) current)
        else match Selection.merge_obj_value incoming existing with
        | None => inl (IncompatibleDuplicates [(n, inr incoming); (n, inr existing)])
        | Some winner =>
            inr (set_filtered_symbol n
              (winner, if bool_decide (winner = existing)
                then add_losing_indexed_presence existing_presence presence
                else add_losing_indexed_presence presence existing_presence)
              current)
        end
    end.

  Definition add_filtered_type (n : name) (incoming : GlobDecl)
      (presence : indexed_location_presence) (current : filtered_indexed_state)
      : construction_error + filtered_indexed_state :=
    if Selection.is_self_type_alias n incoming then inr current else
    match current.(filtered_types) !! n with
    | None => inr (set_filtered_type n (incoming, presence) current)
    | Some (existing, existing_presence) =>
        if bool_decide (incoming = existing) then
          inr (set_filtered_type n (existing,
            merge_indexed_presence existing_presence presence) current)
        else match Selection.merge_glob_decl incoming existing with
        | None => inl (IncompatibleDuplicates [(n, inl incoming); (n, inl existing)])
        | Some winner =>
            inr (set_filtered_type n
              (winner, if bool_decide (winner = existing)
                then add_losing_indexed_presence existing_presence presence
                else add_losing_indexed_presence presence existing_presence)
              current)
        end
    end.

  Definition add_filtered_msymbol (n : name) (incoming : template MObjValue)
      (presence : indexed_location_presence) (current : filtered_indexed_state)
      : construction_error + filtered_indexed_state :=
    match current.(filtered_msymbols) !! n with
    | None => inr (set_filtered_msymbol n (incoming, presence) current)
    | Some (existing, existing_presence) =>
        if bool_decide (incoming = existing) then
          inr (set_filtered_msymbol n (existing,
            merge_indexed_presence existing_presence presence) current)
        else inr (set_filtered_msymbol n (incoming,
          add_losing_indexed_presence presence existing_presence) current)
    end.

  Definition add_filtered_mtype (n : name) (incoming : template MGlobDecl)
      (presence : indexed_location_presence) (current : filtered_indexed_state)
      : construction_error + filtered_indexed_state :=
    match current.(filtered_mtypes) !! n with
    | None => inr (set_filtered_mtype n (incoming, presence) current)
    | Some (existing, existing_presence) =>
        if bool_decide (incoming = existing) then
          inr (set_filtered_mtype n (existing,
            merge_indexed_presence existing_presence presence) current)
        else inr (set_filtered_mtype n (incoming,
          add_losing_indexed_presence presence existing_presence) current)
    end.

  Fixpoint fold_filtered_presence_from
      (events : list filtered_indexed_located_root_event)
      (current : filtered_indexed_state)
      : construction_error + filtered_indexed_state :=
    match events with
    | [] => inr current
    | FILESymbol n value _ _ at_root in_tree :: rest =>
        match fold_filtered_presence_from rest current with
        | inl error => inl error
        | inr next => add_filtered_symbol n value
            {| indexed_presence_at_root := at_root;
               indexed_presence_in_tree := in_tree |} next
        end
    | FILEType n value _ _ at_root in_tree :: rest =>
        match fold_filtered_presence_from rest current with
        | inl error => inl error
        | inr next => add_filtered_type n value
            {| indexed_presence_at_root := at_root;
               indexed_presence_in_tree := in_tree |} next
        end
    | FILEMsymbol n value _ _ at_root in_tree :: rest =>
        match add_filtered_msymbol n value
            {| indexed_presence_at_root := at_root;
               indexed_presence_in_tree := in_tree |} current with
        | inl error => inl error
        | inr next => fold_filtered_presence_from rest next
        end
    | FILEMtype n value _ _ at_root in_tree :: rest =>
        match add_filtered_mtype n value
            {| indexed_presence_at_root := at_root;
               indexed_presence_in_tree := in_tree |} current with
        | inl error => inl error
        | inr next => fold_filtered_presence_from rest next
        end
    end.

  Definition filter_indexed_locations
      (locations : root_locations indexed_location)
      (presence : filtered_indexed_state) : root_locations indexed_location := {|
    symbol_locations := NM.fold (fun n entry result =>
      if entry.2.(indexed_presence_in_tree) then
        match locations.(symbol_locations) !! n with
        | Some location => <[n := location]> result | None => result end
      else result) presence.(filtered_symbols) ∅;
    type_locations := NM.fold (fun n entry result =>
      if entry.2.(indexed_presence_in_tree) then
        match locations.(type_locations) !! n with
        | Some location => <[n := location]> result | None => result end
      else result) presence.(filtered_types) ∅;
    msymbol_locations := TM.fold (fun n entry result =>
      if entry.2.(indexed_presence_in_tree) then
        match locations.(msymbol_locations) !! n with
        | Some location => <[n := location]> result | None => result end
      else result) presence.(filtered_msymbols) ∅;
    mtype_locations := TM.fold (fun n entry result =>
      if entry.2.(indexed_presence_in_tree) then
        match locations.(mtype_locations) !! n with
        | Some location => <[n := location]> result | None => result end
      else result) presence.(filtered_mtypes) ∅
  |}.

  Definition fold_filtered_indexed_events
      (events : list filtered_indexed_located_root_event)
      : construction_error + root_locations indexed_location :=
    let raw_events := List.map filtered_event_indexed events in
    match fold_indexed_events raw_events with
    | inl error => inl error
    | inr locations =>
        match fold_filtered_presence_from events empty_filtered_indexed_state with
        | inl error => inl error
        | inr presence => inr (filter_indexed_locations locations presence)
        end
    end.

  Definition assemble_lazy_compact_indexed_dag_source_map
      (source_files : list source_file)
      (source_origins : Encoded.indexed_provenance)
      (dag : Encoded.indexed_location_dag)
      (singletons : singleton_root_locations)
      (residuals : root_locations indexed_location) : source_map := {|
    files := source_files;
    origin_data := IndexedOrigins source_origins;
    location_data := CompactIndexedLocations dag singletons residuals
  |}.

  Definition build_lazy_compact_indexed_dag_source_map
      (source_files : list source_file)
      (source_origins : Encoded.indexed_provenance)
      (dag : Encoded.indexed_location_dag)
      (singletons : singleton_root_locations)
      (residual_events : list indexed_located_root_event)
      : construction_error + source_map :=
    match fold_indexed_events residual_events with
    | inl error => inl error
    | inr residuals => inr (assemble_lazy_compact_indexed_dag_source_map
        source_files source_origins dag singletons residuals)
    end.

  Ltac build_lazy_compact_indexed_dag_source_map_or_fail
      source_files source_origins dag singletons residual_events :=
    let result := eval vm_compute in (fold_indexed_events residual_events) in
    lazymatch result with
    | inr ?residuals =>
        exact (assemble_lazy_compact_indexed_dag_source_map
          source_files source_origins dag singletons residuals)
    | inl ?error => fail "source-location construction failed:" error
    end.

  Ltac build_filtered_lazy_compact_indexed_dag_source_map_or_fail
      source_files source_origins dag singletons residual_events :=
    let result := eval vm_compute in
      (fold_filtered_indexed_events residual_events) in
    lazymatch result with
    | inr ?residuals =>
        exact (assemble_lazy_compact_indexed_dag_source_map
          source_files source_origins dag singletons residuals)
    | inl ?error => fail "source-location construction failed:" error
    end.
End Construction.
