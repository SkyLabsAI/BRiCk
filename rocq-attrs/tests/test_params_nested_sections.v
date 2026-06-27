(************************************************************************)
(* Nested sections bump arity once per section segment, only for used    *)
(* variables in that segment.                                           *)
(************************************************************************)

Require Import attrs.ParamsAttr.

Section Outer.
  Context {A : Type}.
  Section Inner.
    Context {B : Type}.
    #[params="1"] Definition nested (x : A) : A := x.
    Definition nested_inner : Params nested 1 := ltac:(typeclasses eauto).
  End Inner.
  Definition nested_outer : Params nested 1 := ltac:(typeclasses eauto).
End Outer.

Definition nested_final : Params (@nested) 2 := ltac:(typeclasses eauto).
Fail Definition nested_wrong : Params (@nested) 3 := ltac:(typeclasses eauto).
