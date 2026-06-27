(************************************************************************)
(* #[local, params] inside a section is usable there and dropped at End. *)
(************************************************************************)

Require Import attrs.ParamsAttr.

Section S.
  Context {A : Type}.
  #[local, params="1"] Definition lf_sec (x : A) : A := x.
  Definition lf_sec_here : Params lf_sec 1 := ltac:(typeclasses eauto).
End S.

Fail Definition lf_sec_after : Params (@lf_sec) 2 := ltac:(typeclasses eauto).
