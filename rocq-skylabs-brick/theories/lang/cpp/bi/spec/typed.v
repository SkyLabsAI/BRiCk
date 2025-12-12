Require Import bluerock.iris.extra.bi.prelude.
Require Import bluerock.iris.extra.bi.observe.
Require Import bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.logic.heap_pred.

(** [Typed cls R] states that [R] is a [Rep] predicate for class [cls].
Formally, from [Rep] predicate [R] we can observe [type_ptrR (Tnamed cls)] *)
#[global] Notation Typed cls R :=
  (Observe (type_ptrR (Tnamed cls)) R).

(** [TypedN] states that predicate [R] taking [N] arguments is [Typed] *)
#[global] Notation Typed1 cls R :=
  (∀ a, Typed cls (R a)).
#[global] Notation Typed2 cls R :=
  (∀ b, Typed1 cls (R b)).
#[global] Notation Typed3 cls R :=
  (∀ c, Typed2 cls (R c)).
#[global] Notation Typed4 cls R :=
  (∀ d, Typed3 cls (R d)).
#[global] Notation Typed5 cls R :=
  (∀ e, Typed4 cls (R e)).
#[global] Notation Typed6 cls R :=
  (∀ f, Typed5 cls (R f)).
