From Stdlib Require Import Lists.List.
Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Import Stdlib.ZArith.ZArith.
Require Import skylabs.prelude.pstring.
Require Import skylabs.lang.cpp.syntax.source_location.
Require Import indexed_boundary_values.

#[local] Set Warnings "-abstract-large-number".
#[local] Open Scope pstring_scope.

Definition is_some {A : Type} (value : option A) : bool :=
  match value with
  | Some _ => true
  | None => false
  end.

Example boundary_source_file_is_exact :
  source_locations.(files) =
    (Build_source_file "boundary.cpp" None FKUser true None :: nil).
Proof. vm_compute. reflexivity. Qed.

Example boundary_table_lengths_are_exact :
  match source_locations.(origin_data) with
  | ExpandedOrigins _ => False
  | IndexedOrigins tables =>
      ( tables.(Encoded.presumed_filename_table).(Encoded.table_length)
      , tables.(Encoded.physical_point_table).(Encoded.table_length)
      , tables.(Encoded.presumed_point_table).(Encoded.table_length)
      , tables.(Encoded.range_table).(Encoded.table_length)
      , tables.(Encoded.macro_frame_table).(Encoded.table_length)
      , tables.(Encoded.origin_table).(Encoded.table_length) ) =
      ( 1%uint63, 4096%uint63, 4095%uint63
      , 4096%uint63, 4097%uint63, 8193%uint63 )
  end.
Proof. vm_compute. reflexivity. Qed.

Example boundary_chunk_counts_are_exact :
  match source_locations.(origin_data) with
  | ExpandedOrigins _ => False
  | IndexedOrigins tables =>
      ( Encoded.array_length
          tables.(Encoded.presumed_filename_table).(Encoded.table_chunks)
      , Encoded.array_length
          tables.(Encoded.physical_point_table).(Encoded.table_chunks)
      , Encoded.array_length
          tables.(Encoded.presumed_point_table).(Encoded.table_chunks)
      , Encoded.array_length
          tables.(Encoded.range_table).(Encoded.table_chunks)
      , Encoded.array_length
          tables.(Encoded.macro_frame_table).(Encoded.table_chunks)
      , Encoded.array_length
          tables.(Encoded.origin_table).(Encoded.table_chunks) ) =
      (1, 1, 1, 1, 2, 3)
  end.
Proof. vm_compute. reflexivity. Qed.

Example boundary_rows_close_every_chunk_correctly :
  match source_locations.(origin_data) with
  | ExpandedOrigins _ => False
  | IndexedOrigins tables =>
      ( is_some (Encoded.table_get tables.(Encoded.physical_point_table)
          0%uint63)
      , is_some (Encoded.table_get tables.(Encoded.physical_point_table)
          4095%uint63)
      , is_some (Encoded.table_get tables.(Encoded.physical_point_table)
          4096%uint63)
      , is_some (Encoded.table_get tables.(Encoded.presumed_point_table)
          4094%uint63)
      , is_some (Encoded.table_get tables.(Encoded.presumed_point_table)
          4095%uint63)
      , is_some (Encoded.table_get tables.(Encoded.range_table) 4095%uint63)
      , is_some (Encoded.table_get tables.(Encoded.range_table) 4096%uint63)
      , is_some (Encoded.table_get tables.(Encoded.macro_frame_table)
          4095%uint63)
      , is_some (Encoded.table_get tables.(Encoded.macro_frame_table)
          4096%uint63)
      , is_some (Encoded.table_get tables.(Encoded.macro_frame_table)
          4097%uint63)
      , is_some (Encoded.table_get tables.(Encoded.origin_table) 4095%uint63)
      , is_some (Encoded.table_get tables.(Encoded.origin_table) 4096%uint63)
      , is_some (Encoded.table_get tables.(Encoded.origin_table) 8191%uint63)
      , is_some (Encoded.table_get tables.(Encoded.origin_table) 8192%uint63)
      , is_some (Encoded.table_get tables.(Encoded.origin_table) 8193%uint63) ) =
      ( true, true, false, true, false, true, false, true, true, false,
        true, true, true, true, false )
  end.
Proof. vm_compute. reflexivity. Qed.

Definition decode_boundary_origin
    (id : origin_id) : Encoded.decode_result source_origin :=
  match source_locations.(origin_data) with
  | ExpandedOrigins _ =>
      inl (Encoded.MissingTableEntry Encoded.OriginTable
        (Uint63.of_Z (Z.of_nat id)))
  | IndexedOrigins tables =>
      match Encoded.table_get_nat tables.(Encoded.origin_table) id with
      | None =>
          inl (Encoded.MissingTableEntry Encoded.OriginTable
            (Uint63.of_Z (Z.of_nat id)))
      | Some origin => Encoded.decode_origin_row tables origin
      end
  end.

Definition boundary_point0 : physical_point :=
  Build_physical_point 0 0%N 1%N 1%N.

Definition boundary_range0 : source_range :=
  Build_source_range (Some boundary_point0) None CharacterRange None.

Definition boundary_origin0 : source_origin :=
  Build_source_origin ExplicitOrigin (Some boundary_range0)
    (Some boundary_range0)
    (Some (Build_presumed_point "boundary-logical.cpp" 100%N 101%N))
    (Some (Build_presumed_point "boundary-logical.cpp" 102%N 103%N))
    (Build_macro_frame
      (Some "BOUNDARY_MACRO_0_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx")
      MacroBody None None :: nil)
    (Some boundary_point0) (Some 1) (1 :: nil).

Definition boundary_last_origin : source_origin :=
  Build_source_origin InheritedOrigin None None None None
    (Build_macro_frame
      (Some "BOUNDARY_MACRO_4095_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx")
      MacroBody None None :: nil)
    None None nil.

Example boundary_first_origin_decodes_exactly :
  decode_boundary_origin 0 = inr boundary_origin0.
Proof. vm_compute. reflexivity. Qed.

Example boundary_last_origin_decodes_exactly :
  decode_boundary_origin 8192 = inr boundary_last_origin.
Proof. vm_compute. reflexivity. Qed.

Example boundary_materialized_count_and_order_are_exact :
  match Internal.materialize_origins source_locations.(origin_data) with
  | inl _ => False
  | inr origins =>
      List.length origins = 8193 /\
      List.nth_error origins 0 = Some boundary_origin0 /\
      List.nth_error origins 8192 = Some boundary_last_origin
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.
