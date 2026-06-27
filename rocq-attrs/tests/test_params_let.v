(************************************************************************)
(* Section Let is local-only: works in the section, no End anomaly.      *)
(************************************************************************)

Require Import attrs.ParamsAttr.

Section S.
  #[params="0"] Let foo (x : nat) : nat := x.
  Definition foo_ok : Params foo 0 := ltac:(typeclasses eauto).
End S.
