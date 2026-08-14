From Stdlib Require Import Lists.List.
Require Import skylabs.lang.cpp.syntax.source_location.
Require Import test_20_source_values.

Definition extracted_origins : list source_origin :=
  match Internal.materialize_origins source_locations.(origin_data) with
  | inr origins => origins
  | inl _ => nil
  end.

Example extracted_files_are_nonempty : source_locations.(files) <> nil.
Proof. vm_compute. discriminate. Qed.

Example extracted_origins_are_nonempty : extracted_origins <> nil.
Proof. vm_compute. discriminate. Qed.

Example extracted_origin_ranges_remain_distinct :
    exists origin spelling expansion,
      In origin extracted_origins /\
      origin.(spelling_range) = Some spelling /\
      origin.(expansion_range) = Some expansion /\
      spelling <> expansion.
Proof.
  vm_compute.
  do 3 eexists.
  split; [right; right; left; reflexivity|].
  repeat split; try reflexivity; discriminate.
Qed.

Example extracted_macro_ranges_remain_distinct :
    exists origin frame spelling expansion,
      In origin extracted_origins /\
      In frame origin.(macro_stack) /\
      frame.(macro_spelling) = Some spelling /\
      frame.(macro_expansion) = Some expansion /\
      spelling <> expansion.
Proof.
  vm_compute.
  do 4 eexists.
  split; [right; right; right; right; right; left; reflexivity|].
  split; [left; reflexivity|].
  repeat split; try reflexivity; discriminate.
Qed.

Example extracted_provenance_validates : exists source, source_locations = source.
Proof. eexists. reflexivity. Qed.
