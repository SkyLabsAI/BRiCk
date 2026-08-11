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
  | TreeShapeMismatch (root : decl_root).

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
End Construction.
