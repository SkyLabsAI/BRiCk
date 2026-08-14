Require Import skylabs.lang.cpp.syntax.source_location.
Require Import skylabs.lang.cpp.parser.
Require Import fixture_17_cpp_locations.

#[local] Open Scope pstring_scope.

Definition origin_line (origin : source_origin) : option N :=
  match origin.(spelling_range) with
  | Some range =>
      match range.(range_begin) with
      | Some point => Some point.(point_line)
      | None => None
      end
  | None => None
  end.

Definition generated_uses_indexed_location_dag : bool :=
  match source_locations.(location_data) with
  | ExpandedLocations _ => false
  | IndexedLocations _ _ | CompactIndexedLocations _ _ _ => true
  end.

Example generated_location_storage_is_an_indexed_dag :
  generated_uses_indexed_location_dag = true.
Proof. vm_compute. reflexivity. Qed.

Definition first_line (result : lookup_error + list source_origin) : option N :=
  match result with
  | inr (origin :: _) => origin_line origin
  | _ => None
  end.

Example nested_initializer_origin :
    first_line
      (skylabs.lang.cpp.syntax.source_location.lookup
        source_locations (DRSymbol (Nglobal (Nid "nested_value")))
        [1; 0]) = Some 13%N.
Proof. vm_compute. reflexivity. Qed.
