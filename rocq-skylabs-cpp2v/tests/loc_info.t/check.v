From Stdlib Require Import PrimInt63.
Require Import Stdlib.Array.PArray.
Require Import skylabs.lang.cpp.syntax.
Require test.local_cpp.
Require test.local_static_cpp.
Require test.local_separate_static_cpp.
Require test.local_separate_templates_cpp.
Require test.local_names_cpp.

#[local] Open Scope pstring_scope.

Goal PArray.default local_cpp.file_names = "unknown_file"%pstring.
Proof. reflexivity. Qed.

Goal PArray.default local_cpp.loc_table = dummy_locations.
Proof. reflexivity. Qed.

Goal file dummy_location = 9223372036854775807%uint63 /\
     byte dummy_location = 9223372036854775807%uint63 /\
     line dummy_location = 9223372036854775807%uint63 /\
     column dummy_location = 9223372036854775807%uint63.
Proof. repeat split. Qed.

Goal file_loc dummy_locations = dummy_location /\
     spelling_loc dummy_locations = dummy_location.
Proof. split; reflexivity. Qed.
