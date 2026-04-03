Require Import Stdlib.Strings.PrimString.
Require Import Ltac2.Ltac2.
Require Import skylabs.ltac2.tc_dispatch.lookup.

Ltac2 ext_tactic () := ltac1:(reflexivity).

#[local] Open Scope pstring_scope.

#[export]
Instance nested_inst : Ltac2Lookup (0 = 0) := {
  ltac2_path := "external" :: "tc_dispatch" :: "ltac2" :: "skylabs_tests" :: nil;
  ltac2_name := "ext_tactic";
}.