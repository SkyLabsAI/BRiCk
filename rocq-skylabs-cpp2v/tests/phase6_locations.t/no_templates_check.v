Require Import skylabs.lang.cpp.syntax.source_location.
Require Import skylabs.lang.cpp.parser.
Require Import no_templates_locations.

Definition generated_uses_indexed_location_dag : bool :=
  match source_locations.(location_data) with
  | ExpandedLocations _ => false
  | IndexedLocations _ _ | CompactIndexedLocations _ _ _ => true
  end.

Example generated_location_storage_is_an_indexed_dag :
  generated_uses_indexed_location_dag = true.
Proof. vm_compute. reflexivity. Qed.

Definition template_symbol_location_count : nat :=
  match source_locations.(location_data) with
  | ExpandedLocations roots => TM.cardinal roots.(msymbol_locations)
  | IndexedLocations _ roots => TM.cardinal roots.(msymbol_locations)
  | CompactIndexedLocations _ singletons residuals =>
      List.length singletons.(singleton_msymbol_locations) +
      TM.cardinal residuals.(msymbol_locations)
  end.

Definition template_type_location_count : nat :=
  match source_locations.(location_data) with
  | ExpandedLocations roots => TM.cardinal roots.(mtype_locations)
  | IndexedLocations _ roots => TM.cardinal roots.(mtype_locations)
  | CompactIndexedLocations _ singletons residuals =>
      List.length singletons.(singleton_mtype_locations) +
      TM.cardinal residuals.(mtype_locations)
  end.

Example template_symbol_locations_are_empty :
  template_symbol_location_count = 0.
Proof. vm_compute. reflexivity. Qed.

Example template_type_locations_are_empty :
  template_type_location_count = 0.
Proof. vm_compute. reflexivity. Qed.
