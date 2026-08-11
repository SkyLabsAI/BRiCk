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
    declarations := locations
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
End Construction.
