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
Require Import skylabs.prelude.pstring.
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
[lookup] below is deliberately the sole location-tree/provenance query API;
[lookup_file] is a checked accessor for file IDs. There is no zipper, ancestor
fallback, isolated-value lookup, or path-preservation promise across later
semantic transformations.
*)

Record file_id : Set := Build_file_id {
  file_id_value : PrimInt63.int
}.

Record origin_id : Set := Build_origin_id {
  origin_id_value : PrimInt63.int
}.

Definition parse_file_id
    (value : PrimInt63.pos_neg_int63) : option file_id :=
  option_map Build_file_id (PrimInt63.parser value).

Definition print_file_id (value : file_id) : PrimInt63.pos_neg_int63 :=
  PrimInt63.printer (PrimInt63.wrap_int value.(file_id_value)).

Definition parse_origin_id
    (value : PrimInt63.pos_neg_int63) : option origin_id :=
  option_map Build_origin_id (PrimInt63.parser value).

Definition print_origin_id (value : origin_id) : PrimInt63.pos_neg_int63 :=
  PrimInt63.printer (PrimInt63.wrap_int value.(origin_id_value)).

Declare Scope file_id_scope.
Delimit Scope file_id_scope with file_id.
Bind Scope file_id_scope with file_id.
Number Notation file_id parse_file_id print_file_id : file_id_scope.

Declare Scope origin_id_scope.
Delimit Scope origin_id_scope with origin_id.
Bind Scope origin_id_scope with origin_id.
Number Notation origin_id parse_origin_id print_origin_id : origin_id_scope.

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

(** Source paths are stored relative to the directory containing the generated
    AST [.v] file. [relative_path_parents] removes directory components before
    [relative_path_components] are appended. Components never contain path
    separators, [.], or [..]. *)
Record relative_path : Set := Build_relative_path {
  relative_path_parents : N;
  relative_path_components : list PrimString.string
}.

(** A source name is either non-filesystem text, a path relative to the AST
    file, or a path below a caller-supplied stable root. Generated files never
    contain an absolute filesystem root. *)
Inductive source_name : Set :=
| LiteralSourceName (name : PrimString.string)
| AstRelativeSourceName (path : relative_path)
| NamedRootSourceName
    (root : PrimString.string) (components : list PrimString.string).

(** Structured absolute paths are supplied by importing proofs, not generated
    AST files. Keeping the root structured makes resolution independent of the
    proof host's path separator conventions. *)
Inductive path_root : Set :=
| PosixPathRoot
| WindowsDrivePathRoot (drive : PrimString.string)
| WindowsUncPathRoot
    (server : PrimString.string) (share : PrimString.string).

Record absolute_path : Set := Build_absolute_path {
  absolute_path_root : path_root;
  absolute_path_components : list PrimString.string
}.

Definition named_root_environment : Set :=
  list (PrimString.string * absolute_path).

Inductive resolved_source_name : Set :=
| ResolvedLiteralSourceName (name : PrimString.string)
| ResolvedSourcePath (path : absolute_path).

Module SourcePath.
  Definition valid_component (component : PrimString.string) : bool :=
    match PrimString.compare component (PrimString.make 0 0%uint63) with
    | Eq => false
    | _ =>
        match PrimString.compare component "." with
        | Eq => false
        | _ =>
            match PrimString.compare component ".." with
            | Eq => false
            | _ =>
                let slash := PrimString.make 1%uint63 (Uint63.of_Z 47) in
                let backslash := PrimString.make 1%uint63 (Uint63.of_Z 92) in
                negb (pstring.contains slash component ||
                      pstring.contains backslash component)
            end
        end
    end.

  Definition valid_components (components : list PrimString.string) : bool :=
    List.forallb valid_component components.

  Definition directory (path : absolute_path) : option absolute_path :=
    match path.(absolute_path_components) with
    | nil => None
    | _ :: _ =>
        Some (Build_absolute_path path.(absolute_path_root)
          (List.removelast path.(absolute_path_components)))
    end.

  Definition apply_relative
      (base : absolute_path) (path : relative_path) : option absolute_path :=
    let components := base.(absolute_path_components) in
    if valid_components components &&
       valid_components path.(relative_path_components) then
      if N.leb path.(relative_path_parents)
          (N.of_nat (List.length components)) then
        let parents := N.to_nat path.(relative_path_parents) in
        Some (Build_absolute_path base.(absolute_path_root)
          (List.firstn (List.length components - parents) components ++
           path.(relative_path_components)))
      else None
    else None.

  Fixpoint find_named_root
      (name : PrimString.string) (roots : named_root_environment)
      : option absolute_path :=
    match roots with
    | nil => None
    | (candidate, path) :: roots =>
        match PrimString.compare name candidate with
        | Eq => Some path
        | _ => find_named_root name roots
        end
    end.

  Definition resolve
      (ast_file : absolute_path) (roots : named_root_environment)
      (name : source_name) : option resolved_source_name :=
    match name with
    | LiteralSourceName literal => Some (ResolvedLiteralSourceName literal)
    | AstRelativeSourceName path =>
        match directory ast_file with
        | Some ast_directory =>
            option_map ResolvedSourcePath (apply_relative ast_directory path)
        | None => None
        end
    | NamedRootSourceName root components =>
        match find_named_root root roots with
        | Some base =>
            if valid_components base.(absolute_path_components) &&
               valid_components components then
              Some (ResolvedSourcePath
                (Build_absolute_path base.(absolute_path_root)
                  (base.(absolute_path_components) ++ components)))
            else None
        | None => None
        end
    end.
End SourcePath.

Record source_file : Set := {
  source_file_physical_name : source_name;
  source_file_requested_name : option source_name;
  source_file_kind : file_kind;
  source_file_is_main : bool;
  source_file_include_parent : option (file_id * PrimInt63.int)
}.

Record physical_point : Set := {
  point_file : file_id;
  point_byte_offset : PrimInt63.int;
  point_line : PrimInt63.int;
  point_byte_column : PrimInt63.int
}.

Record presumed_point : Set := {
  presumed_file : source_name;
  presumed_line : PrimInt63.int;
  presumed_column : PrimInt63.int
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
    [loc_path]. Public nominal IDs wrap the corresponding primitive row ID. *)
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
      never observable. Private table IDs and wrapped public row IDs both use
      primitive integers; [nat] conversion remains only for diagnostic APIs. *)
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

  Record encoded_physical_point : Set := {
    encoded_point_file : table_id;
    encoded_point_byte_offset : PrimInt63.int;
    encoded_point_line : PrimInt63.int;
    encoded_point_byte_column : PrimInt63.int
  }.

  Record encoded_presumed_point : Set := {
    encoded_presumed_file : table_id;
    encoded_presumed_line : PrimInt63.int;
    encoded_presumed_column : PrimInt63.int
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
    encoded_anchor_origin : option table_id;
    encoded_derived_from : list table_id
  }.

  Record indexed_provenance : Type := {
    presumed_filename_table : indexed_table source_name;
    physical_point_table : indexed_table encoded_physical_point;
    presumed_point_table : indexed_table encoded_presumed_point;
    range_table : indexed_table encoded_range;
    macro_frame_table : indexed_table encoded_macro_frame;
    origin_table : indexed_table encoded_origin
  }.

  Record encoded_location_shape : Set := {
    encoded_shape_children : list table_id
  }.

  Record encoded_location_node : Set := {
    encoded_node_shape : table_id;
    encoded_node_origins : list table_id;
    encoded_node_children : list table_id
  }.

  Record indexed_location_dag : Type := {
    location_shape_table : indexed_table encoded_location_shape;
    location_node_table : indexed_table encoded_location_node
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
    let! point := fetch PhysicalPointTable tables.(physical_point_table) id in
    inr (Build_physical_point (Build_file_id point.(encoded_point_file))
      point.(encoded_point_byte_offset) point.(encoded_point_line)
      point.(encoded_point_byte_column)).

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
      (option_map Build_origin_id origin.(encoded_anchor_origin))
      (List.map Build_origin_id origin.(encoded_derived_from))).

  Definition default_presumed_filename : source_name :=
    LiteralSourceName (PrimString.make 0 0%uint63).
  Definition default_encoded_physical_point : encoded_physical_point :=
    Build_encoded_physical_point 0%uint63 0%uint63 0%uint63 0%uint63.
  Definition default_encoded_presumed_point : encoded_presumed_point :=
    Build_encoded_presumed_point 0%uint63 0%uint63 0%uint63.
  Definition default_encoded_range : encoded_range :=
    EncodedRawRange None None TokenRange.
  Definition default_encoded_macro_frame : encoded_macro_frame :=
    Build_encoded_macro_frame None MacroBody None None.
  Definition default_encoded_origin : encoded_origin :=
    Build_encoded_origin ExplicitOrigin None None None None [] None None [].
  Definition default_encoded_location_shape : encoded_location_shape :=
    Build_encoded_location_shape [].
  Definition default_encoded_location_node : encoded_location_node :=
    Build_encoded_location_node 0%uint63 [] [].
End Encoded.

Inductive loc_tree (A : Type) : Type :=
| LocNode (here : list A) (children : list (loc_tree A)).

#[global] Arguments LocNode {A} _ _.

Record root_locations (A : Type) : Type := {
  symbol_locations : NM.t A;
  type_locations : NM.t A;
  msymbol_locations : TM.t A;
  mtype_locations : TM.t A
}.

#[global] Arguments symbol_locations {A} _.
#[global] Arguments type_locations {A} _.
#[global] Arguments msymbol_locations {A} _.
#[global] Arguments mtype_locations {A} _.

Definition declaration_locations (A : Type) : Type :=
  root_locations (loc_tree A).

Inductive indexed_location : Type :=
| StaticLocation (node shape : Encoded.table_id)
| MergeLocations
    (shape : Encoded.table_id)
    (existing incoming : indexed_location)
| AddRootOrigins
    (shape : Encoded.table_id)
    (winner loser : indexed_location).

Definition indexed_location_shape
    (location : indexed_location) : Encoded.table_id :=
  match location with
  | StaticLocation _ shape => shape
  | MergeLocations shape _ _ => shape
  | AddRootOrigins shape _ _ => shape
  end.

(** Generated proposal-4 companions keep producer-certified singleton roots as
    data instead of constructing a board-scale AVL map during compilation.
    Namespace-specific lists avoid irrelevant scans. Residual duplicate and
    conservative typedef groups remain in ordinary selected root maps. *)
Record singleton_root_locations : Type := {
  singleton_symbol_locations : list (name * indexed_location);
  singleton_type_locations : list (name * indexed_location);
  singleton_msymbol_locations : list (name * indexed_location);
  singleton_mtype_locations : list (name * indexed_location)
}.

Inductive location_store : Type :=
| ExpandedLocations (roots : declaration_locations origin_id)
| IndexedLocations
    (dag : Encoded.indexed_location_dag)
    (roots : root_locations indexed_location)
| CompactIndexedLocations
    (dag : Encoded.indexed_location_dag)
    (singletons : singleton_root_locations)
    (residuals : root_locations indexed_location).

Inductive origin_store : Type :=
| ExpandedOrigins (values : list source_origin)
| IndexedOrigins (tables : Encoded.indexed_provenance).

Record source_map : Type := {
  files : list source_file;
  origin_data : origin_store;
  location_data : location_store
}.

Inductive decl_root : Set :=
| DRSymbol (name : name)
| DRType (name : name)
| DRMsymbol (name : name)
| DRMtype (name : name).

Inductive location_table_kind : Set :=
| LocationShapeTable
| LocationNodeTable.

Inductive location_dag_error : Set :=
| MissingLocationTableEntry
    (table : location_table_kind) (id : Encoded.table_id)
| LocationNodeShapeMismatch
    (node declared actual : Encoded.table_id)
| LocationArityMismatch
    (node shape : Encoded.table_id)
    (node_arity shape_arity : nat)
| LocationCompositionShapeMismatch
    (declared actual : Encoded.table_id)
| NonBackwardLocationNodeEdge
    (parent child : Encoded.table_id)
| NonBackwardLocationShapeEdge
    (parent child : Encoded.table_id).

Inductive compact_location_error : Set :=
| DuplicateSingletonLocation
| SingletonResidualLocationCollision.

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
    (error : Encoded.decode_error)
| MalformedLocationDag
    (root : decl_root)
    (consumed_depth : nat)
    (error : location_dag_error)
| MalformedCompactLocations
    (root : decl_root)
    (error : compact_location_error).

Module Internal.
  Definition find_root {A : Type}
      (locations : root_locations A) (root : decl_root) : option A :=
    match root with
    | DRSymbol n => locations.(symbol_locations) !! n
    | DRType n => locations.(type_locations) !! n
    | DRMsymbol n => locations.(msymbol_locations) !! n
    | DRMtype n => locations.(mtype_locations) !! n
    end.

  Definition singleton_entries
      (locations : singleton_root_locations) (root : decl_root)
      : list (name * indexed_location) :=
    match root with
    | DRSymbol _ => locations.(singleton_symbol_locations)
    | DRType _ => locations.(singleton_type_locations)
    | DRMsymbol _ => locations.(singleton_msymbol_locations)
    | DRMtype _ => locations.(singleton_mtype_locations)
    end.

  Definition root_name (root : decl_root) : name :=
    match root with
    | DRSymbol n | DRType n | DRMsymbol n | DRMtype n => n
    end.

  Fixpoint find_unique_singleton
      (wanted : name) (entries : list (name * indexed_location))
      (found : option indexed_location)
      : compact_location_error + option indexed_location :=
    match entries with
    | [] => inr found
    | (candidate, location) :: rest =>
        if bool_decide (candidate = wanted) then
          match found with
          | Some _ => inl DuplicateSingletonLocation
          | None => find_unique_singleton wanted rest (Some location)
          end
        else find_unique_singleton wanted rest found
    end.

  Definition find_compact_root
      (singletons : singleton_root_locations)
      (residuals : root_locations indexed_location) (root : decl_root)
      : lookup_error + option indexed_location :=
    match find_unique_singleton (root_name root)
        (singleton_entries singletons root) None with
    | inl error => inl (MalformedCompactLocations root error)
    | inr singleton =>
        match singleton, find_root residuals root with
        | Some _, Some _ => inl (MalformedCompactLocations root
            SingletonResidualLocationCollision)
        | Some location, None | None, Some location => inr (Some location)
        | None, None => inr None
        end
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

  Definition fetch_location_shape
      (dag : Encoded.indexed_location_dag) (id : Encoded.table_id)
      : location_dag_error + Encoded.encoded_location_shape :=
    match Encoded.table_get dag.(Encoded.location_shape_table) id with
    | Some shape => inr shape
    | None => inl (MissingLocationTableEntry LocationShapeTable id)
    end.

  Definition fetch_location_node
      (dag : Encoded.indexed_location_dag) (id : Encoded.table_id)
      : location_dag_error + Encoded.encoded_location_node :=
    match Encoded.table_get dag.(Encoded.location_node_table) id with
    | Some node => inr node
    | None => inl (MissingLocationTableEntry LocationNodeTable id)
    end.

  Definition validate_static_location
      (dag : Encoded.indexed_location_dag)
      (node_id shape_id : Encoded.table_id)
      : location_dag_error +
          (Encoded.encoded_location_node * Encoded.encoded_location_shape) :=
    match fetch_location_node dag node_id with
    | inl error => inl error
    | inr node =>
        match fetch_location_shape dag shape_id with
        | inl error => inl error
        | inr shape =>
            if PrimInt63.eqb node.(Encoded.encoded_node_shape) shape_id then
              let node_arity := List.length
                node.(Encoded.encoded_node_children) in
              let shape_arity := List.length
                shape.(Encoded.encoded_shape_children) in
              if Nat.eqb node_arity shape_arity then inr (node, shape)
              else inl (LocationArityMismatch node_id shape_id
                node_arity shape_arity)
            else inl (LocationNodeShapeMismatch node_id shape_id
              node.(Encoded.encoded_node_shape))
        end
    end.

  Definition composition_shape
      (declared : Encoded.table_id) (location : indexed_location)
      : option location_dag_error :=
    let actual := indexed_location_shape location in
    if PrimInt63.eqb declared actual then None
    else Some (LocationCompositionShapeMismatch declared actual).

  Definition static_location_child
      (root : decl_root) (consumed index : nat)
      (dag : Encoded.indexed_location_dag)
      (node_id shape_id : Encoded.table_id)
      : lookup_error + indexed_location :=
    match validate_static_location dag node_id shape_id with
    | inl error => inl (MalformedLocationDag root consumed error)
    | inr (node, shape) =>
        let node_children := node.(Encoded.encoded_node_children) in
        let shape_children := shape.(Encoded.encoded_shape_children) in
        match nth_error node_children index, nth_error shape_children index with
        | Some child_node, Some child_shape =>
            if (child_node <? node_id)%uint63 then
              if (child_shape <? shape_id)%uint63 then
                inr (StaticLocation child_node child_shape)
              else inl (MalformedLocationDag root consumed
                (NonBackwardLocationShapeEdge shape_id child_shape))
            else inl (MalformedLocationDag root consumed
              (NonBackwardLocationNodeEdge node_id child_node))
        | None, None =>
            inl (ChildOutOfBounds root consumed index
              (List.length node_children))
        | _, _ =>
            inl (MalformedLocationDag root consumed
              (LocationArityMismatch node_id shape_id
                (List.length node_children) (List.length shape_children)))
        end
    end.

  Fixpoint indexed_location_child
      (root : decl_root) (consumed index : nat)
      (dag : Encoded.indexed_location_dag) (location : indexed_location)
      : lookup_error + indexed_location :=
    match location with
    | StaticLocation node shape =>
        static_location_child root consumed index dag node shape
    | MergeLocations shape existing incoming =>
        match composition_shape shape existing with
        | Some error => inl (MalformedLocationDag root consumed error)
        | None =>
            match composition_shape shape incoming with
            | Some error => inl (MalformedLocationDag root consumed error)
            | None =>
                match indexed_location_child root consumed index dag existing with
                | inl error => inl error
                | inr existing_child =>
                    match indexed_location_child root consumed index dag incoming with
                    | inl error => inl error
                    | inr incoming_child =>
                        let child_shape :=
                          indexed_location_shape existing_child in
                        match composition_shape child_shape incoming_child with
                        | Some error =>
                            inl (MalformedLocationDag root consumed error)
                        | None => inr (MergeLocations child_shape
                            existing_child incoming_child)
                        end
                    end
                end
            end
        end
    | AddRootOrigins shape winner _ =>
        match composition_shape shape winner with
        | Some error => inl (MalformedLocationDag root consumed error)
        | None => indexed_location_child root consumed index dag winner
        end
    end.

  Fixpoint indexed_location_origins
      (root : decl_root) (consumed : nat)
      (dag : Encoded.indexed_location_dag) (location : indexed_location)
      : lookup_error + list Encoded.table_id :=
    match location with
    | StaticLocation node_id shape_id =>
        match validate_static_location dag node_id shape_id with
        | inl error => inl (MalformedLocationDag root consumed error)
        | inr (node, _) => inr node.(Encoded.encoded_node_origins)
        end
    | MergeLocations shape existing incoming =>
        match composition_shape shape existing with
        | Some error => inl (MalformedLocationDag root consumed error)
        | None =>
            match composition_shape shape incoming with
            | Some error => inl (MalformedLocationDag root consumed error)
            | None =>
                match indexed_location_origins root consumed dag existing with
                | inl error => inl error
                | inr existing_origins =>
                    match indexed_location_origins root consumed dag incoming with
                    | inl error => inl error
                    | inr incoming_origins =>
                        inr (existing_origins ++ incoming_origins)
                    end
                end
            end
        end
    | AddRootOrigins shape winner loser =>
        match composition_shape shape winner with
        | Some error => inl (MalformedLocationDag root consumed error)
        | None =>
            match indexed_location_origins root consumed dag winner with
            | inl error => inl error
            | inr winner_origins =>
                match indexed_location_origins root consumed dag loser with
                | inl error => inl error
                | inr loser_origins => inr (winner_origins ++ loser_origins)
                end
            end
        end
    end.

  Fixpoint descend_indexed
      (root : decl_root) (consumed : nat) (path : loc_path)
      (dag : Encoded.indexed_location_dag) (location : indexed_location)
      : lookup_error + list Encoded.table_id :=
    match path with
    | [] => indexed_location_origins root consumed dag location
    | index :: rest =>
        match indexed_location_child root consumed index dag location with
        | inl error => inl error
        | inr child => descend_indexed root (S consumed) rest dag child
        end
    end.

  Fixpoint list_get_table_id {A : Type}
      (values : list A) (index : Encoded.table_id) : option A :=
    match values with
    | [] => None
    | value :: rest =>
        if PrimInt63.eqb index 0%uint63 then Some value
        else list_get_table_id rest (PrimInt63.sub index 1%uint63)
    end.

  Definition list_get_origin_id {A : Type}
      (values : list A) (id : origin_id) : option A :=
    list_get_table_id values id.(origin_id_value).

  Definition valid_expanded_origin_id
      (all_origins : list source_origin) (id : origin_id) : bool :=
    match list_get_origin_id all_origins id with
    | Some _ => true
    | None => false
    end.

  Inductive indexed_origin_access : Type :=
  | IndexedOriginFound (origin : Encoded.encoded_origin)
  | IndexedOriginLogicalOutOfBounds
  | IndexedOriginStorageMissing.

  Definition indexed_origin_at
      (tables : Encoded.indexed_provenance) (id : Encoded.table_id)
      : indexed_origin_access :=
    let origins := tables.(Encoded.origin_table) in
    if (id <? origins.(Encoded.table_length))%uint63 then
      match Encoded.table_get origins id with
      | Some origin => IndexedOriginFound origin
      | None => IndexedOriginStorageMissing
      end
    else IndexedOriginLogicalOutOfBounds.

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
  | IndexedReferenceOutOfBounds (id : Encoded.table_id)
  | IndexedReferenceStorageMissing (id : Encoded.table_id).

  Definition check_indexed_reference
      (tables : Encoded.indexed_provenance) (id : Encoded.table_id)
      : option indexed_reference_error :=
    match indexed_origin_at tables id with
    | IndexedOriginFound _ => None
    | IndexedOriginLogicalOutOfBounds =>
        Some (IndexedReferenceOutOfBounds id)
    | IndexedOriginStorageMissing =>
        Some (IndexedReferenceStorageMissing id)
    end.

  Fixpoint first_invalid_indexed_id
      (tables : Encoded.indexed_provenance) (ids : list Encoded.table_id)
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
        match list_get_origin_id all_origins id with
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
        match indexed_origin_at tables id.(origin_id_value) with
        | IndexedOriginLogicalOutOfBounds =>
            inl (OriginIdOutOfBounds root path id)
        | IndexedOriginStorageMissing =>
            inl (MalformedProvenance root path id
              (Encoded.MissingTableEntry Encoded.OriginTable
                id.(origin_id_value)))
        | IndexedOriginFound origin =>
            match first_invalid_indexed_reference tables origin with
            | Some (IndexedReferenceOutOfBounds bad) =>
                inl (OriginIdOutOfBounds root path (Build_origin_id bad))
            | Some (IndexedReferenceStorageMissing bad) =>
                inl (MalformedProvenance root path id
                  (Encoded.MissingTableEntry Encoded.OriginTable bad))
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

  Fixpoint validate_shape_children
      (parent : Encoded.table_id) (children : list Encoded.table_id)
      : option location_dag_error :=
    match children with
    | [] => None
    | child :: rest =>
        if (child <? parent)%uint63 then
          validate_shape_children parent rest
        else Some (NonBackwardLocationShapeEdge parent child)
    end.

  Fixpoint validate_location_shapes_from
      (dag : Encoded.indexed_location_dag) (remaining : nat)
      (index : Encoded.table_id) : option location_dag_error :=
    match remaining with
    | O => None
    | S remaining =>
        match fetch_location_shape dag index with
        | inl error => Some error
        | inr shape =>
            match validate_shape_children index
                shape.(Encoded.encoded_shape_children) with
            | Some error => Some error
            | None => validate_location_shapes_from dag remaining
                (PrimInt63.add index 1%uint63)
            end
        end
    end.

  Fixpoint validate_location_node_children
      (dag : Encoded.indexed_location_dag) (parent : Encoded.table_id)
      (node_children shape_children : list Encoded.table_id)
      : option location_dag_error :=
    match node_children, shape_children with
    | [], [] => None
    | child_node :: node_rest, child_shape :: shape_rest =>
        if (child_node <? parent)%uint63 then
          match fetch_location_node dag child_node with
          | inl error => Some error
          | inr child =>
              if PrimInt63.eqb child.(Encoded.encoded_node_shape)
                  child_shape then
                validate_location_node_children dag parent
                  node_rest shape_rest
              else Some (LocationNodeShapeMismatch child_node child_shape
                child.(Encoded.encoded_node_shape))
          end
        else Some (NonBackwardLocationNodeEdge parent child_node)
    | _, _ => Some (LocationArityMismatch parent 0%uint63
        (List.length node_children) (List.length shape_children))
    end.

  Fixpoint validate_location_nodes_from
      (dag : Encoded.indexed_location_dag) (remaining : nat)
      (index : Encoded.table_id) : option location_dag_error :=
    match remaining with
    | O => None
    | S remaining =>
        match fetch_location_node dag index with
        | inl error => Some error
        | inr node =>
            let shape_id := node.(Encoded.encoded_node_shape) in
            match fetch_location_shape dag shape_id with
            | inl error => Some error
            | inr shape =>
                let node_children := node.(Encoded.encoded_node_children) in
                let shape_children := shape.(Encoded.encoded_shape_children) in
                if Nat.eqb (List.length node_children)
                    (List.length shape_children) then
                  match validate_location_node_children dag index
                      node_children shape_children with
                  | Some error => Some error
                  | None => validate_location_nodes_from dag remaining
                      (PrimInt63.add index 1%uint63)
                  end
                else Some (LocationArityMismatch index shape_id
                  (List.length node_children) (List.length shape_children))
            end
        end
    end.

  (** Explicitly eager diagnostic validation. Production construction and
      [lookup] never call it; lookup checks only rows reached by its root/path. *)
  Definition validate_location_dag
      (dag : Encoded.indexed_location_dag) : option location_dag_error :=
    match validate_location_shapes_from dag
        (Encoded.table_length_nat dag.(Encoded.location_shape_table))
        0%uint63 with
    | Some error => Some error
    | None => validate_location_nodes_from dag
        (Encoded.table_length_nat dag.(Encoded.location_node_table)) 0%uint63
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

(** Checked access to the stable first-seen file table. The primitive wrapper
    is traversed against the list itself, so even a maximal malformed ID cannot
    force construction of a large unary [nat]. *)
Definition lookup_file
    (map : source_map) (id : file_id) : option source_file :=
  Internal.list_get_table_id map.(files) id.(file_id_value).

(** The only supported location-tree/provenance query operation. Errors are [inl],
    success is [inr], and compact provenance is decoded only for origins at the
    selected semantic node. A successful node with no origins returns [inr []]. *)
Definition lookup
    (map : source_map) (root : decl_root) (path : loc_path)
    : lookup_error + list source_origin :=
  match map.(location_data) with
  | ExpandedLocations locations =>
      match Internal.find_root locations root with
      | None => inl (RootNotFound root)
      | Some tree =>
          match Internal.descend root 0 path tree with
          | inl error => inl error
          | inr (LocNode ids _) =>
              match map.(origin_data) with
              | ExpandedOrigins origins =>
                  Internal.resolve_expanded_origins root path origins ids
              | IndexedOrigins tables =>
                  Internal.resolve_indexed_origins root path tables ids
              end
          end
      end
  | IndexedLocations dag locations =>
      match Internal.find_root locations root with
      | None => inl (RootNotFound root)
      | Some location =>
          match Internal.descend_indexed root 0 path dag location with
          | inl error => inl error
          | inr raw_ids =>
              let ids := List.map Build_origin_id raw_ids in
              match map.(origin_data) with
              | ExpandedOrigins origins =>
                  Internal.resolve_expanded_origins root path origins ids
              | IndexedOrigins tables =>
                  Internal.resolve_indexed_origins root path tables ids
              end
          end
      end
  | CompactIndexedLocations dag singletons residuals =>
      match Internal.find_compact_root singletons residuals root with
      | inl error => inl error
      | inr None => inl (RootNotFound root)
      | inr (Some location) =>
          match Internal.descend_indexed root 0 path dag location with
          | inl error => inl error
          | inr raw_ids =>
              let ids := List.map Build_origin_id raw_ids in
              match map.(origin_data) with
              | ExpandedOrigins origins =>
                  Internal.resolve_expanded_origins root path origins ids
              | IndexedOrigins tables =>
                  Internal.resolve_indexed_origins root path tables ids
              end
          end
      end
  end.
