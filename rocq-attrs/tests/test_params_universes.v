(************************************************************************)
(* Polymorphic sources get polymorphic generated Params instances.       *)
(************************************************************************)

Require Import attrs.ParamsAttr.

#[params="1"] Polymorphic Definition qid@{u} (A : Type@{u}) (x : A) : A := x.

Universe u v.
Constraint u < v.
Definition qid_inst_u : Params (@qid@{u}) 1 := ltac:(typeclasses eauto).
Definition qid_inst_v : Params (@qid@{v}) 1 := ltac:(typeclasses eauto).
