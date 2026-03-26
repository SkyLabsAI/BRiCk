Require Import skylabs.ltac2.tc_dispatch.lookup.
Require Import Stdlib.Strings.PrimString.

#[local] Open Scope pstring_scope.

Module Import Nested.
  Ltac2 inside_module () := ltac1:(reflexivity).
  Instance nested_inst : Ltac2Lookup (0 = 0) := {
    ltac2_path := "Nested" :: "nested" :: "tc_dispatch" :: "ltac2" :: "skylabs_tests" :: nil;
    ltac2_name := "inside_module";
  }.
End Nested.

Example test_success_nested : 0 = 0.
Proof.
  goal_dispatch. (* Should resolve Nested.inside_module *)
Qed.
