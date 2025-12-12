(*
 * Copyright (c) 2020-21 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import stdpp.countable.
Require Import bluerock.prelude.numbers.
Require Import bluerock.prelude.list_numbers.


Section type.
  #[local] Set Primitive Projections.
  (** A generic wrapper for types isomorphic to N *)
  Record WrapN {Phant : Set} : Set := MkWrapN { unwrapN : N }.
End type.
Add Printing Constructor WrapN.

Arguments WrapN Phant : clear implicits.
Arguments MkWrapN {Phant} _ : assert.

Notation Build_WrapN := @MkWrapN (only parsing).

(* Using the wrapper means we define these instances/lemmas only once. *)

Lemma cancel_unwrapN {Phant} (x : WrapN Phant) : MkWrapN (unwrapN x) = x.
Proof. done. Qed.

Lemma cancel_MkwrapN {Phant} n : unwrapN (Phant := Phant) (MkWrapN n) = n.
Proof. done. Qed.

#[global] Instance cancel_unwrapN_Build_WrapN {Phant} :
  Cancel eq unwrapN (@MkWrapN Phant).
Proof. exact cancel_MkwrapN. Qed.

#[global] Instance cancel_Build_WrapN_unwrapN {Phant} :
  Cancel eq (@MkWrapN Phant) unwrapN.
Proof. exact cancel_unwrapN. Qed.

#[global] Instance wrapN_eq_decision {Phant} : EqDecision (WrapN Phant).
Proof. solve_decision. Defined.

#[global] Instance wrapN_countable {Phant} : Countable (WrapN Phant) :=
  inj_countable' unwrapN MkWrapN cancel_unwrapN.

#[global] Instance wrapN_inhabited {Phant} : Inhabited (WrapN Phant) :=
  populate (MkWrapN 0).

#[global] Instance unwrapN_inj Phant : Inj eq eq (@unwrapN Phant).
Proof. intros [] [] ?. by simplify_eq/=. Qed.

#[global] Instance MkWrapN_inj Phant : Inj eq eq (@MkWrapN Phant).
Proof. by intros ?? [=]. Qed.

#[global] Declare Scope wrapN_scope.
#[global] Delimit Scope wrapN_scope with wrapN.
(* ^ it would be nicer to have one delimiting key per instantiation of WrapN,
    but that doesn't seem possible? *)
#[global] Bind Scope wrapN_scope with WrapN.

Module Import wrapN_notations.
  Class WrapNAdd {T U R : Set} := wrapN_add : T -> U -> R.
  #[global] Instance wrapNN_add {Phant} : @WrapNAdd (WrapN Phant) N (WrapN Phant) :=
    fun w n => MkWrapN (unwrapN w + n).
  #[global] Instance NwrapN_add {Phant} : @WrapNAdd N (WrapN Phant) (WrapN Phant) :=
    fun n w => MkWrapN (n + unwrapN w).
  #[global] Instance wrapNwrapN_add {Phant} : @WrapNAdd (WrapN Phant) (WrapN Phant) (WrapN Phant) :=
    fun w1 w2 => MkWrapN (unwrapN w1 + unwrapN w2).
  Notation "0" := (MkWrapN 0) (only parsing) : wrapN_scope.
  Infix "+" := wrapN_add (only parsing) : wrapN_scope.
End wrapN_notations.

#[global] Arguments wrapNN_add {_} _ _ /.
#[global] Arguments NwrapN_add {_} _ _ /.
#[global] Arguments wrapNwrapN_add {_} _ _ /.
#[global] Arguments wrapN_add {T U R _} _ _ /.

Section seqW.
  Context {Phant : Set}.
  Implicit Types (w : WrapN Phant).
  #[local] Open Scope wrapN_scope.

  Lemma wrapN_add_0N_l w : 0%N + w = w.
  Proof. by rewrite /= N.add_0_l. Qed.
  Lemma wrapN_add_0w_l w : 0 + w = w.
  Proof. by rewrite /= N.add_0_l. Qed.
  Lemma wrapN_add_0N_r w : w + 0%N = w.
  Proof. by rewrite /= N.add_0_r. Qed.
  Lemma wrapN_add_0w_r w : w + 0 = w.
  Proof. by rewrite /= N.add_0_r. Qed.

  Definition wrapN_succ w : WrapN Phant :=
    MkWrapN $ N.succ $ unwrapN w.

  Lemma unwrapN_succ_inj w : unwrapN (wrapN_succ w) = N.succ (unwrapN w).
  Proof. done. Qed.

  Definition seqW w (sz : N) : list (WrapN Phant) :=
    MkWrapN <$> seqN (unwrapN w) sz.

  Lemma cons_seqW len start :
    start :: seqW (wrapN_succ start) len = seqW start (N.succ len).
  Proof. by rewrite /seqW -cons_seqN. Qed.

  (* Lifts [seqN_S_end_app] *)
  Lemma seqW_S_end_app w n : seqW w (N.succ n) = seqW w n ++ [w + n].
  Proof. by rewrite /seqW seqN_S_end_app fmap_app. Qed.

  Lemma cons_seqW' [len start] sstart :
    sstart = wrapN_succ start ->
    start :: seqW sstart len = seqW start (N.succ len).
  Proof. move->. apply cons_seqW. Qed.

  Lemma seqW_S_end_app' [w n] sn :
    sn = N.succ n ->
    seqW w sn = seqW w n ++ [w + n].
  Proof. move->. apply seqW_S_end_app. Qed.
End seqW.

Module Type wrapper.
  Variant Phant : Set :=.	(** i.e., empty *)

  Definition t := WrapN Phant.

  (** Beware this is not actually (super)global:
  https://github.com/coq/coq/issues/14988 *)
  #[global] Bind Scope wrapN_scope with t.

  Definition of_N : N -> t := MkWrapN.
  Definition to_N : t -> N := unwrapN.
  Lemma of_to_N x : of_N (to_N x) = x.
  Proof. apply cancel_unwrapN. Qed.
  Lemma to_of_N x : to_N (of_N x) = x.
  Proof. apply (inj of_N). by rewrite of_to_N. Qed.

End wrapper.

Module Type succ_wrapper (Import W : wrapper).
  Notation succ := (wrapN_succ (Phant := Phant) : t -> t) (only parsing).
  Notation seqW := (seqW (Phant := Phant) : (t -> N -> list t)) (only parsing).
End succ_wrapper.

(**
Example usage for [wrapper]:
Module your_type.
  (* Include wrapper. *) (* Or *)
  Include val_wrapper. (* Using [val_wrap.v] *)

  Include succ_wrapper. (* If appropriate for your type. *)
End your_type.

(* Workaround https://github.com/coq/coq/issues/14988 *)
#[global] Bind Scope wrapN_scope with your_type.t.

 *)
