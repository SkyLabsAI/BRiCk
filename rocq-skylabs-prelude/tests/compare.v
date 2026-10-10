Require Import skylabs.prelude.base.
Require Import skylabs.prelude.compare.

Import compare.Notations.

Section comparison_notation.
  Context `{!Compare A}.

  (** Comparison notation refers to the comparator without requiring its laws. *)
  Example comparison_notation (x y : A) :
    (x ?= y) = compare x y /\
    (x ?=@{A} y) = compare x y /\
    (?=) x y = compare x y /\
    (?=@{A}) x y = compare x y /\
    (x ?=.) y = compare x y /\
    (.?= y) x = compare x y.
  Proof. repeat split; reflexivity. Qed.
End comparison_notation.
