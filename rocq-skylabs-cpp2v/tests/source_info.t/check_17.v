From Stdlib Require Import Lists.List.
Require Import skylabs.lang.cpp.syntax.source_location.
Require Import test_17_source_values.

Example extracted_files_are_nonempty : source_locations.(files) <> nil.
Proof. vm_compute. discriminate. Qed.

Example extracted_origins_are_nonempty : source_locations.(origins) <> nil.
Proof. vm_compute. discriminate. Qed.

Example extracted_provenance_validates : exists source, source_locations = source.
Proof. eexists. reflexivity. Qed.
