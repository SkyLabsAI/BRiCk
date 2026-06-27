Require Import attrs.ParamsAttr.

#[params="0"] Definition global_f (x : nat) : nat := x.

Section GlobalSection.
  Context {A : Type}.
  #[params="1"] Definition global_sec (x : A) : A := x.
  Definition global_sec_here : Params global_sec 1 := ltac:(typeclasses eauto).
End GlobalSection.

Definition global_sec_after : Params (@global_sec) 2 := ltac:(typeclasses eauto).
Fail Definition global_sec_old : Params (@global_sec) 1 := ltac:(typeclasses eauto).
