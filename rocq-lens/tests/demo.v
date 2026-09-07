Require Import elpi.apps.derive.derive.
Require Import Lens.Lens.
Require Import Lens.Elpi.Elpi.

Import LensNotations.
#[local] Open Scope lens_scope.

#[projections(primitive=no)]
Record NoPP : Set := { field : nat }.

#[only(lens)] derive NoPP.

About _field.

#[projections(primitive=yes)]
Record Foo : Set := {
  foo : nat;
  bar : bool;
}.

#[only(lens)] derive Foo.

About _foo.
About _bar.

Goal {| foo := 3 ; bar := true |} .^ _foo = 3.
Proof. reflexivity. Qed.

Goal {| foo := 3 ; bar := true |} .^ _bar = true.
Proof. reflexivity. Qed.

Goal {| foo := 3 ; bar := true |} &: _bar .= false =
     {| foo := 3 ; bar := false |}.
Proof. reflexivity. Qed.

Set Printing All.

(* Test for https://github.com/LPCIC/coq-elpi/pull/521 *)
Goal forall r, foo r = 0 -> view _foo r = foo r.
Proof.
  intros r H.
  simpl.
  Show.
  rewrite H.
  Show.
  reflexivity.
Qed.
