Require Import attrs.ParamsAttr.

#[local, params="0"] Definition local_f (x : nat) : nat := x.
Definition local_f_here : Params local_f 0 := ltac:(typeclasses eauto).

Section LocalSection.
  Context {A : Type}.
  #[local, params="1"] Definition local_sec (x : A) : A := x.
  Definition local_sec_here : Params local_sec 1 := ltac:(typeclasses eauto).
End LocalSection.

Fail Definition local_sec_after : Params (@local_sec) 2 := ltac:(typeclasses eauto).
