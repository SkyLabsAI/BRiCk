Require Import skylabs.prelude.base.
Require Import skylabs.prelude.compare.

Import compare.Notations.

Section comparison_notation.
  Context `{!Compare A}.

  (** Comparison notation refers to the comparator without requiring its laws. *)
  Example comparison_notation (x y : A) :
    (x ?= y) = base.compare x y /\
    (x ?=@{A} y) = base.compare x y /\
    (?=) x y = base.compare x y /\
    (?=@{A}) x y = base.compare x y /\
    (x ?=.) y = base.compare x y /\
    (.?= y) x = base.compare x y.
  Proof. repeat split; reflexivity. Qed.
End comparison_notation.
