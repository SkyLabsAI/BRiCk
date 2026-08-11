(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Stdlib.Array.PArray.
Require Import Stdlib.NArith.BinNat.
Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Import Stdlib.Strings.PrimString.
Require Import Stdlib.ZArith.ZArith.
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

(** Compact, first-seen source-provenance tables used by generated companions.
    Table identities are private representation details and never occur in
    [loc_path]. Public [origin_id] values retain their original [nat] rows. *)
Module Encoded.
  Definition table_id : Set := PrimInt63.int.

  (** A 4096-entry inner chunk keeps every primitive array well below Rocq's
      limit while two levels cover the complete producer [uint32_t] ID space. *)
  Definition table_chunk_size : table_id := 4096%uint63.

  Record indexed_table (A : Type) : Type := {
    table_length : table_id;
    table_chunks : PArray.array (PArray.array A)
  }.

  #[global] Arguments Build_indexed_table {A} _ _.
  #[global] Arguments table_length {A} _.
  #[global] Arguments table_chunks {A} _.

  Definition array_length {A : Type} (values : PArray.array A) : nat :=
    Z.to_nat (Uint63.to_Z (PArray.length values)).

  Definition table_length_nat {A : Type} (table : indexed_table A) : nat :=
    Z.to_nat (Uint63.to_Z table.(table_length)).

  Definition nat_to_table_id (index : nat) : option table_id :=
    let encoded := Z.of_nat index in
    if (encoded <=? Uint63.to_Z Uint63.max_int)%Z then
      Some (Uint63.of_Z encoded)
    else None.

  (** Bounds are checked before [PArray.get], so a primitive-array default is
      never observable. Private IDs are primitive integers; only public
      [origin_id] values require a checked conversion from [nat]. *)
  Definition array_get {A : Type}
      (values : PArray.array A) (index : table_id) : option A :=
    if (index <? PArray.length values)%uint63 then
      Some (PArray.get values index)
    else None.

  Definition table_get {A : Type}
      (table : indexed_table A) (index : table_id) : option A :=
    if (index <? table.(table_length))%uint63 then
      let chunk_index := PrimInt63.div index table_chunk_size in
      let item_index := PrimInt63.mod index table_chunk_size in
      match array_get table.(table_chunks) chunk_index with
      | Some chunk => array_get chunk item_index
      | None => None
      end
    else None.

  Definition table_get_nat {A : Type}
      (table : indexed_table A) (index : nat) : option A :=
    match nat_to_table_id index with
    | Some encoded => table_get table encoded
    | None => None
    end.

  Record encoded_presumed_point : Set := {
    encoded_presumed_file : table_id;
    encoded_presumed_line : N;
    encoded_presumed_column : N
  }.

  Inductive encoded_range : Set :=
  | EncodedRawRange
      (begin end_ : option table_id) (kind : range_kind)
  | EncodedSameBeginRange
      (begin end_ : table_id) (kind : range_kind)
      (normalized_end : table_id)
  | EncodedGeneralRange
      (begin end_ : table_id) (kind : range_kind)
      (normalized_begin normalized_end : table_id).

  Record encoded_macro_frame : Set := {
    encoded_macro_name : option PrimString.string;
    encoded_macro_kind : macro_origin_kind;
    encoded_macro_spelling : option table_id;
    encoded_macro_expansion : option table_id
  }.

  Inductive encoded_macro_occurrence : Set :=
  | InlineMacroFrame (frame : encoded_macro_frame)
  | MacroFrameReference (frame : table_id).

  Record encoded_origin : Set := {
    encoded_origin_class : origin_kind;
    encoded_spelling_range : option table_id;
    encoded_expansion_range : option table_id;
    encoded_presumed_begin : option table_id;
    encoded_presumed_end : option table_id;
    encoded_macro_stack : list encoded_macro_occurrence;
    encoded_point_of_instantiation : option table_id;
    encoded_anchor_origin : option origin_id;
    encoded_derived_from : list origin_id
  }.

  Record indexed_provenance : Type := {
    presumed_filename_table : indexed_table PrimString.string;
    physical_point_table : indexed_table physical_point;
    presumed_point_table : indexed_table encoded_presumed_point;
    range_table : indexed_table encoded_range;
    macro_frame_table : indexed_table encoded_macro_frame;
    origin_table : indexed_table encoded_origin
  }.

  Inductive table_kind : Set :=
  | PresumedFilenameTable
  | PhysicalPointTable
  | PresumedPointTable
  | RangeTable
  | MacroFrameTable
  | OriginTable.

  Inductive decode_error : Set :=
  | MissingTableEntry (table : table_kind) (id : table_id).

  Definition decode_result (A : Type) : Type := decode_error + A.

  Definition decode_bind {A B : Type}
      (value : decode_result A) (next : A -> decode_result B)
      : decode_result B :=
    match value with
    | inl error => inl error
    | inr decoded => next decoded
    end.

  #[local] Notation "'let!' x ':=' value 'in' body" :=
    (decode_bind value (fun x => body))
      (at level 200, x name, value at level 100, body at level 200).

  Definition fetch {A : Type}
      (kind : table_kind) (table : indexed_table A) (id : table_id)
      : decode_result A :=
    match table_get table id with
    | Some value => inr value
    | None => inl (MissingTableEntry kind id)
    end.

  Definition decode_optional {A : Type}
      (decode : table_id -> decode_result A) (id : option table_id)
      : decode_result (option A) :=
    match id with
    | None => inr None
    | Some value =>
        let! decoded := decode value in
        inr (Some decoded)
    end.

  Definition decode_point
      (tables : indexed_provenance) (id : table_id)
      : decode_result physical_point :=
    fetch PhysicalPointTable tables.(physical_point_table) id.

  Definition decode_presumed_point
      (tables : indexed_provenance) (id : table_id)
      : decode_result presumed_point :=
    let! point := fetch PresumedPointTable tables.(presumed_point_table) id in
    let! file := fetch PresumedFilenameTable tables.(presumed_filename_table)
      point.(encoded_presumed_file) in
    inr (Build_presumed_point file point.(encoded_presumed_line)
      point.(encoded_presumed_column)).

  Definition decode_range_row
      (tables : indexed_provenance) (range : encoded_range)
      : decode_result source_range :=
    match range with
    | EncodedRawRange begin end_ kind =>
        let! decoded_begin := decode_optional (decode_point tables) begin in
        let! decoded_end := decode_optional (decode_point tables) end_ in
        inr (Build_source_range decoded_begin decoded_end kind None)
    | EncodedSameBeginRange begin end_ kind normalized_end =>
        let! decoded_begin := decode_point tables begin in
        let! decoded_end := decode_point tables end_ in
        let! decoded_normalized_end := decode_point tables normalized_end in
        inr (Build_source_range (Some decoded_begin) (Some decoded_end) kind
          (Some (decoded_begin, decoded_normalized_end)))
    | EncodedGeneralRange begin end_ kind normalized_begin normalized_end =>
        let! decoded_begin := decode_point tables begin in
        let! decoded_end := decode_point tables end_ in
        let! decoded_normalized_begin := decode_point tables normalized_begin in
        let! decoded_normalized_end := decode_point tables normalized_end in
        inr (Build_source_range (Some decoded_begin) (Some decoded_end) kind
          (Some (decoded_normalized_begin, decoded_normalized_end)))
    end.

  Definition decode_range
      (tables : indexed_provenance) (id : table_id)
      : decode_result source_range :=
    let! range := fetch RangeTable tables.(range_table) id in
    decode_range_row tables range.

  Definition decode_macro_frame_row
      (tables : indexed_provenance) (frame : encoded_macro_frame)
      : decode_result macro_frame :=
    let! spelling := decode_optional (decode_range tables)
      frame.(encoded_macro_spelling) in
    let! expansion := decode_optional (decode_range tables)
      frame.(encoded_macro_expansion) in
    inr (Build_macro_frame frame.(encoded_macro_name)
      frame.(encoded_macro_kind) spelling expansion).

  Definition decode_macro_occurrence
      (tables : indexed_provenance) (occurrence : encoded_macro_occurrence)
      : decode_result macro_frame :=
    match occurrence with
    | InlineMacroFrame frame => decode_macro_frame_row tables frame
    | MacroFrameReference id =>
        let! frame := fetch MacroFrameTable tables.(macro_frame_table) id in
        decode_macro_frame_row tables frame
    end.

  Fixpoint decode_macro_stack
      (tables : indexed_provenance) (stack : list encoded_macro_occurrence)
      : decode_result (list macro_frame) :=
    match stack with
    | [] => inr []
    | occurrence :: rest =>
        let! frame := decode_macro_occurrence tables occurrence in
        let! decoded_rest := decode_macro_stack tables rest in
        inr (frame :: decoded_rest)
    end.

  Definition decode_origin_row
      (tables : indexed_provenance) (origin : encoded_origin)
      : decode_result source_origin :=
    let! spelling := decode_optional (decode_range tables)
      origin.(encoded_spelling_range) in
    let! expansion := decode_optional (decode_range tables)
      origin.(encoded_expansion_range) in
    let! presumed_begin := decode_optional (decode_presumed_point tables)
      origin.(encoded_presumed_begin) in
    let! presumed_end := decode_optional (decode_presumed_point tables)
      origin.(encoded_presumed_end) in
    let! macro_stack := decode_macro_stack tables
      origin.(encoded_macro_stack) in
    let! point_of_instantiation := decode_optional (decode_point tables)
      origin.(encoded_point_of_instantiation) in
    inr (Build_source_origin origin.(encoded_origin_class) spelling expansion
      presumed_begin presumed_end macro_stack point_of_instantiation
      origin.(encoded_anchor_origin) origin.(encoded_derived_from)).

  Definition default_presumed_filename : PrimString.string :=
    PrimString.make 0 0%uint63.
  Definition default_physical_point : physical_point :=
    Build_physical_point 0 0%N 0%N 0%N.
  Definition default_encoded_presumed_point : encoded_presumed_point :=
    Build_encoded_presumed_point 0%uint63 0%N 0%N.
  Definition default_encoded_range : encoded_range :=
    EncodedRawRange None None TokenRange.
  Definition default_encoded_macro_frame : encoded_macro_frame :=
    Build_encoded_macro_frame None MacroBody None None.
  Definition default_encoded_origin : encoded_origin :=
    Build_encoded_origin ExplicitOrigin None None None None [] None None [].
End Encoded.

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

Inductive origin_store : Type :=
| ExpandedOrigins (values : list source_origin)
| IndexedOrigins (tables : Encoded.indexed_provenance).

Record source_map : Type := {
  files : list source_file;
  origin_data : origin_store;
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
    (id : origin_id)
| MalformedProvenance
    (root : decl_root)
    (path : loc_path)
    (origin : origin_id)
    (error : Encoded.decode_error).

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

  Definition valid_expanded_origin_id
      (all_origins : list source_origin) (id : origin_id) : bool :=
    match nth_error all_origins id with
    | Some _ => true
    | None => false
    end.

  Inductive indexed_origin_access : Type :=
  | IndexedOriginFound (origin : Encoded.encoded_origin)
  | IndexedOriginLogicalOutOfBounds
  | IndexedOriginStorageMissing.

  Definition indexed_origin_at
      (tables : Encoded.indexed_provenance) (id : origin_id)
      : indexed_origin_access :=
    let origins := tables.(Encoded.origin_table) in
    match Encoded.nat_to_table_id id with
    | None => IndexedOriginLogicalOutOfBounds
    | Some encoded =>
        if (encoded <? origins.(Encoded.table_length))%uint63 then
          match Encoded.table_get origins encoded with
          | Some origin => IndexedOriginFound origin
          | None => IndexedOriginStorageMissing
          end
        else IndexedOriginLogicalOutOfBounds
    end.

  Fixpoint first_invalid_id
      (valid : origin_id -> bool) (ids : list origin_id)
      : option origin_id :=
    match ids with
    | [] => None
    | id :: rest =>
        if valid id then first_invalid_id valid rest else Some id
    end.

  (** Lookup checks the immediate references of each returned origin. Global
      provenance-graph acyclicity is a producer/IRValidator invariant, not a
      second query-time graph traversal. *)
  Definition first_invalid_expanded_reference
      (all_origins : list source_origin) (origin : source_origin)
      : option origin_id :=
    let valid := valid_expanded_origin_id all_origins in
    match origin.(anchor_origin) with
    | Some id =>
        if valid id then first_invalid_id valid origin.(derived_from)
        else Some id
    | None => first_invalid_id valid origin.(derived_from)
    end.

  Inductive indexed_reference_error : Set :=
  | IndexedReferenceOutOfBounds (id : origin_id)
  | IndexedReferenceStorageMissing (id : origin_id).

  Definition check_indexed_reference
      (tables : Encoded.indexed_provenance) (id : origin_id)
      : option indexed_reference_error :=
    match indexed_origin_at tables id with
    | IndexedOriginFound _ => None
    | IndexedOriginLogicalOutOfBounds =>
        Some (IndexedReferenceOutOfBounds id)
    | IndexedOriginStorageMissing =>
        Some (IndexedReferenceStorageMissing id)
    end.

  Fixpoint first_invalid_indexed_id
      (tables : Encoded.indexed_provenance) (ids : list origin_id)
      : option indexed_reference_error :=
    match ids with
    | [] => None
    | id :: rest =>
        match check_indexed_reference tables id with
        | Some error => Some error
        | None => first_invalid_indexed_id tables rest
        end
    end.

  Definition first_invalid_indexed_reference
      (tables : Encoded.indexed_provenance)
      (origin : Encoded.encoded_origin) : option indexed_reference_error :=
    match origin.(Encoded.encoded_anchor_origin) with
    | Some id =>
        match check_indexed_reference tables id with
        | Some error => Some error
        | None =>
            first_invalid_indexed_id tables
              origin.(Encoded.encoded_derived_from)
        end
    | None =>
        first_invalid_indexed_id tables origin.(Encoded.encoded_derived_from)
    end.

  Fixpoint resolve_expanded_origins
      (root : decl_root) (path : loc_path)
      (all_origins : list source_origin) (ids : list origin_id)
      : lookup_error + list source_origin :=
    match ids with
    | [] => inr []
    | id :: rest =>
        match nth_error all_origins id with
        | None => inl (OriginIdOutOfBounds root path id)
        | Some origin =>
            match first_invalid_expanded_reference all_origins origin with
            | Some bad => inl (OriginIdOutOfBounds root path bad)
            | None =>
                match resolve_expanded_origins root path all_origins rest with
                | inl err => inl err
                | inr resolved => inr (origin :: resolved)
                end
            end
        end
    end.

  Fixpoint resolve_indexed_origins
      (root : decl_root) (path : loc_path)
      (tables : Encoded.indexed_provenance) (ids : list origin_id)
      : lookup_error + list source_origin :=
    match ids with
    | [] => inr []
    | id :: rest =>
        match indexed_origin_at tables id with
        | IndexedOriginLogicalOutOfBounds =>
            inl (OriginIdOutOfBounds root path id)
        | IndexedOriginStorageMissing =>
            inl (MalformedProvenance root path id
              (Encoded.MissingTableEntry Encoded.OriginTable
                (Uint63.of_Z (Z.of_nat id))))
        | IndexedOriginFound origin =>
            match first_invalid_indexed_reference tables origin with
            | Some (IndexedReferenceOutOfBounds bad) =>
                inl (OriginIdOutOfBounds root path bad)
            | Some (IndexedReferenceStorageMissing bad) =>
                inl (MalformedProvenance root path id
                  (Encoded.MissingTableEntry Encoded.OriginTable
                    (Uint63.of_Z (Z.of_nat bad))))
            | None =>
                match Encoded.decode_origin_row tables origin with
                | inl error => inl (MalformedProvenance root path id error)
                | inr decoded =>
                    match resolve_indexed_origins root path tables rest with
                    | inl error => inl error
                    | inr resolved => inr (decoded :: resolved)
                    end
                end
            end
        end
    end.

  (** Deliberately eager diagnostic support. Generated construction and public
      [lookup] never call this materializer. *)
  Fixpoint materialize_indexed_from
      (tables : Encoded.indexed_provenance) (remaining : nat)
      (index : Encoded.table_id)
      : Encoded.decode_result (list source_origin) :=
    match remaining with
    | O => inr []
    | S remaining =>
        match Encoded.table_get tables.(Encoded.origin_table) index with
        | None => inl (Encoded.MissingTableEntry Encoded.OriginTable index)
        | Some origin =>
            match Encoded.decode_origin_row tables origin with
            | inl error => inl error
            | inr decoded =>
                match materialize_indexed_from tables remaining
                    (PrimInt63.add index 1%uint63) with
                | inl error => inl error
                | inr rest => inr (decoded :: rest)
                end
            end
        end
    end.

  Definition materialize_origins
      (store : origin_store) : Encoded.decode_result (list source_origin) :=
    match store with
    | ExpandedOrigins origins => inr origins
    | IndexedOrigins tables =>
        materialize_indexed_from tables
          (Encoded.table_length_nat tables.(Encoded.origin_table)) 0%uint63
    end.
End Internal.

(** The only supported source-location query operation. Errors are [inl],
    success is [inr], and compact provenance is decoded only for origins at the
    selected semantic node. A successful node with no origins returns [inr []]. *)
Definition lookup
    (map : source_map) (root : decl_root) (path : loc_path)
    : lookup_error + list source_origin :=
  match Internal.find_root map.(declarations) root with
  | None => inl (RootNotFound root)
  | Some tree =>
      match Internal.descend root 0 path tree with
      | inl err => inl err
      | inr (LocNode ids _) =>
          match map.(origin_data) with
          | ExpandedOrigins origins =>
              Internal.resolve_expanded_origins root path origins ids
          | IndexedOrigins tables =>
              Internal.resolve_indexed_origins root path tables ids
          end
      end
  end.
