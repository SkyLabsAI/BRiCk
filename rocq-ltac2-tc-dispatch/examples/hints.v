Require Import Ltac2.Ltac2.
Require Import Stdlib.Strings.PrimString.
Require Import Stdlib.Lists.List.
Require Import skylabs.ltac2.tc_crush.db.

Module for_tauto.
  Ltac2 for_True () := ltac1:(trivial).
  Ltac2 for_False () := ltac1:(contradiction).
  Ltac2 for_and () := ltac1:(split).
  Ltac2 for_impl () := ltac1:(intro).

  #[local] Open Scope pstring.

  Definition for_True : Ltac2Lookup True :=
  {| ltac2_path := "for_tauto" :: "hints" :: "tc_crush" :: "ltac2" :: "skylabs" :: nil
  ; ltac2_name := "for_True" |}.

  Definition for_False : Ltac2Lookup False :=
  {| ltac2_path := "for_tauto" :: "hints" :: "tc_crush" :: "ltac2" :: "skylabs" :: nil
   ; ltac2_name := "for_False" |}.

  Definition for_and {P Q : Prop} : Ltac2Lookup (P /\ Q) :=
  {| ltac2_path := "for_tauto" :: "hints" :: "tc_crush" :: "ltac2" :: "skylabs" :: nil
   ; ltac2_name := "for_and" |}.

  Definition for_impl {P Q : Prop} : Ltac2Lookup (P -> Q) :=
  {| ltac2_path := "for_tauto" :: "hints" :: "tc_crush" :: "ltac2" :: "skylabs" :: nil
   ; ltac2_name := "for_impl" |}.

  #[global] Hint Resolve for_True for_False for_and for_impl | 0 : crush_ext.
End for_tauto.
