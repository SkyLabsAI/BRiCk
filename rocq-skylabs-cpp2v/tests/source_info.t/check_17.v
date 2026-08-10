From Stdlib Require Import Lists.List.
Require Import skylabs.lang.cpp.syntax.source_location.
Require Import test_17_source_values.

Example extracted_files_are_nonempty : source_locations.(files) <> nil.
Proof. vm_compute. discriminate. Qed.

Example extracted_origins_are_nonempty : source_locations.(origins) <> nil.
Proof. vm_compute. discriminate. Qed.

Example extracted_origin_ranges_remain_distinct :
    exists origin spelling expansion,
      In origin source_locations.(origins) /\
      origin.(spelling_range) = Some spelling /\
      origin.(expansion_range) = Some expansion /\
      spelling <> expansion.
Proof. vm_compute. eauto 20. Qed.

Example extracted_macro_ranges_remain_distinct :
    exists origin frame spelling expansion,
      In origin source_locations.(origins) /\
      In frame origin.(macro_stack) /\
      frame.(macro_spelling) = Some spelling /\
      frame.(macro_expansion) = Some expansion /\
      spelling <> expansion.
Proof. vm_compute. eauto 30. Qed.

Example extracted_provenance_validates : exists source, source_locations = source.
Proof. eexists. reflexivity. Qed.
