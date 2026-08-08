(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Stdlib.NArith.BinNat.
Require Import Stdlib.Strings.PrimString.
Require Import stdpp.fin_maps.
Require Import skylabs.lang.cpp.syntax.core.
Require Import skylabs.lang.cpp.syntax.namemap.

(**
Persistent source provenance and the arity-shaped location sidecar.

The path ABI follows semantic recursive fields, not printer syntax. Lists,
options, products, and sums contribute their recursive payloads but never add a
node. In particular, adding or reordering a recursive BRiCk field requires a
matching IR-constructor registry, checked factory, [Arena::children] test,
and path-fixture update in the same change.

The map is keyed only by the four name-bearing translation-unit root kinds.
[lookup] below is deliberately the sole query API: there is no zipper,
ancestor fallback, isolated-value lookup, or path-preservation promise across
later semantic transformations.
*)

Definition file_id : Set := nat.
Definition origin_id : Set := nat.
Definition loc_path : Set := list nat.

Inductive file_kind : Set :=
| FKUser
| FKSystem
| FKExternCSystem
| FKUserModuleMap
| FKSystemModuleMap
| FKBuiltin
| FKCommandLine
| FKScratch
| FKPredefined
| FKOther.

Record source_file : Set := {
  source_file_physical_name : PrimString.string;
  source_file_requested_name : option PrimString.string;
  source_file_kind : file_kind;
  source_file_is_main : bool;
  source_file_include_parent : option (file_id * N)
}.

Record physical_point : Set := {
  point_file : file_id;
  point_byte_offset : N;
  point_line : N;
  point_byte_column : N
}.

Record presumed_point : Set := {
  presumed_file : PrimString.string;
  presumed_line : N;
  presumed_column : N
}.

Inductive range_kind : Set :=
| TokenRange
| CharacterRange.

Record source_range : Set := {
  range_begin : option physical_point;
  range_end : option physical_point;
  range_end_semantics : range_kind;
  normalized_half_open : option (physical_point * physical_point)
}.

Inductive macro_origin_kind : Set :=
| MacroBody
| MacroArgument.

Record macro_frame : Set := {
  macro_name : option PrimString.string;
  macro_kind : macro_origin_kind;
  macro_spelling : option source_range;
  macro_expansion : option source_range
}.

Inductive origin_kind : Set :=
| ExplicitOrigin
| ImplicitOrigin
| ClangTransformedOrigin
| Cpp2vSynthesizedOrigin
| InheritedOrigin.

Record source_origin : Set := {
  origin_class : origin_kind;
  spelling_range : option source_range;
  expansion_range : option source_range;
  presumed_begin : option presumed_point;
  presumed_end : option presumed_point;
  macro_stack : list macro_frame;
  point_of_instantiation : option physical_point;
  anchor_origin : option origin_id;
  derived_from : list origin_id
}.

Inductive loc_tree (A : Type) : Type :=
| LocNode (here : list A) (children : list (loc_tree A)).

#[global] Arguments LocNode {A} _ _.

Record declaration_locations (A : Type) : Type := {
  symbol_locations : NM.t (loc_tree A);
  type_locations : NM.t (loc_tree A);
  msymbol_locations : TM.t (loc_tree A);
  mtype_locations : TM.t (loc_tree A)
}.

#[global] Arguments symbol_locations {A} _.
#[global] Arguments type_locations {A} _.
#[global] Arguments msymbol_locations {A} _.
#[global] Arguments mtype_locations {A} _.

Record source_map : Type := {
  files : list source_file;
  origins : list source_origin;
  declarations : declaration_locations origin_id
}.

Inductive decl_root : Set :=
| DRSymbol (name : name)
| DRType (name : name)
| DRMsymbol (name : name)
| DRMtype (name : name).

Inductive lookup_error : Set :=
| RootNotFound (root : decl_root)
| ChildOutOfBounds
    (root : decl_root)
    (consumed_depth : nat)
    (requested_index : nat)
    (available_children : nat)
| OriginIdOutOfBounds
    (root : decl_root)
    (path : loc_path)
    (id : origin_id).

Module Internal.
  Definition find_root
      (locations : declaration_locations origin_id) (root : decl_root)
      : option (loc_tree origin_id) :=
    match root with
    | DRSymbol n => locations.(symbol_locations) !! n
    | DRType n => locations.(type_locations) !! n
    | DRMsymbol n => locations.(msymbol_locations) !! n
    | DRMtype n => locations.(mtype_locations) !! n
    end.

  Fixpoint descend
      (root : decl_root) (consumed : nat) (path : loc_path)
      (tree : loc_tree origin_id)
      : lookup_error + loc_tree origin_id :=
    match path with
    | [] => inr tree
    | index :: rest =>
        match tree with
        | LocNode _ children =>
            match nth_error children index with
            | Some child => descend root (S consumed) rest child
            | None =>
                inl (ChildOutOfBounds root consumed index (length children))
            end
        end
    end.

  Definition valid_origin_id
      (all_origins : list source_origin) (id : origin_id) : bool :=
    match nth_error all_origins id with
    | Some _ => true
    | None => false
    end.

  Fixpoint first_invalid_id
      (all_origins : list source_origin) (ids : list origin_id)
      : option origin_id :=
    match ids with
    | [] => None
    | id :: rest =>
        if valid_origin_id all_origins id then first_invalid_id all_origins rest
        else Some id
    end.

  (** Lookup checks the immediate references of each returned origin. Global
      provenance-graph acyclicity is a producer/IRValidator invariant, not a
      second query-time graph traversal. *)
  Definition first_invalid_reference
      (all_origins : list source_origin) (origin : source_origin)
      : option origin_id :=
    match origin.(anchor_origin) with
    | Some id =>
        if valid_origin_id all_origins id then
          first_invalid_id all_origins origin.(derived_from)
        else Some id
    | None => first_invalid_id all_origins origin.(derived_from)
    end.

  Fixpoint resolve_origins
      (root : decl_root) (path : loc_path)
      (all_origins : list source_origin) (ids : list origin_id)
      : lookup_error + list source_origin :=
    match ids with
    | [] => inr []
    | id :: rest =>
        match nth_error all_origins id with
        | None => inl (OriginIdOutOfBounds root path id)
        | Some origin =>
            match first_invalid_reference all_origins origin with
            | Some bad => inl (OriginIdOutOfBounds root path bad)
            | None =>
                match resolve_origins root path all_origins rest with
                | inl err => inl err
                | inr resolved => inr (origin :: resolved)
                end
            end
        end
    end.
End Internal.

(** The only source-location query operation. Errors are [inl], success is
    [inr]. A successful node with no origins returns [inr []]. *)
Definition lookup
    (map : source_map) (root : decl_root) (path : loc_path)
    : lookup_error + list source_origin :=
  match Internal.find_root map.(declarations) root with
  | None => inl (RootNotFound root)
  | Some tree =>
      match Internal.descend root 0 path tree with
      | inl err => inl err
      | inr (LocNode ids _) =>
          Internal.resolve_origins root path map.(origins) ids
      end
  end.
