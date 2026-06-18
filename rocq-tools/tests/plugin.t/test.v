Require Import skylabs.perf_data_collector.perf_data_collector.

(* "*)" *)

Inductive N :=
  | O : N
  | S : N -> N.

Fixpoint add (n m : N) : N :=
  match n with
  | O => m
  | S n => S (add n m)
  end.
