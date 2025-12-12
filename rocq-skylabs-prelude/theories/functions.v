(*
 * Copyright (c) 2022 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import stdpp.functions.
Require Import bluerock.prelude.base.
Require Import bluerock.prelude.axioms.funext.

(* Belongs in stdpp or prelude. *)
#[global] Instance fn_lookup_total {A T} : LookupTotal A T (A → T) := λ a f, f a.

Lemma fn_lookup_total_unfold {A T} (f : A → T) (a : A) :
  f !!! a = f a.
Proof. done. Qed.

Section dep_fn_insert.
  Context {A : Type} `{EqDecision A} {T : A -> Type}.
  Implicit Types (a : A).

  Import EqNotations.

  (** Dependent version of [ <[ a0 := t ]> f ] *)
  Definition dep_fn_insert a0 (t : T a0) (f : ∀ a : A, T a) : ∀ a : A, T a :=
    fun a =>
    match decide (a0 = a) with
    | left E => rew E in t
    | right _ => f a
    end.


  (* Lemmas below are named after the lens laws. *)

  Lemma dep_fn_insert_view_set f a0 t :
    dep_fn_insert a0 t f a0 = t.
  Proof. by rewrite /dep_fn_insert decide_True_pi. Qed.

  Lemma dep_fn_insert_view_set' f a0 a t (E : a0 = a):
    dep_fn_insert a0 t f a = rew E in t.
  Proof. destruct E. apply dep_fn_insert_view_set. Qed.

  Lemma dep_fn_insert_view_set_ne f a0 a t (NE : a0 <> a) :
    dep_fn_insert a0 t f a = f a.
  Proof. rewrite /dep_fn_insert. by case_decide as E. Qed.

  Lemma dep_fn_insert_set_view (f : ∀ a, T a) a0 a :
    dep_fn_insert a0 (f a0) f a = f a.
  Proof.
    destruct (decide (a = a0)) as [-> | ].
    by rewrite dep_fn_insert_view_set.
    by rewrite dep_fn_insert_view_set_ne.
  Qed.

  Lemma dep_fn_insert_set_set (f : ∀ a, T a) a0 (t1 t2 : T a0) a :
    dep_fn_insert a0 t2 (dep_fn_insert a0 t1 f) a =
    dep_fn_insert a0 t2 f a.
  Proof.
    destruct (decide (a = a0)) as [-> | ].
    by rewrite !dep_fn_insert_view_set.
    by rewrite !dep_fn_insert_view_set_ne.
  Qed.

  Lemma dep_fn_insert_exchange (f : ∀ a, T a) (a0 a1 a : A) t0 t1 :
    a0 <> a1 ->
    dep_fn_insert a1 t1 (dep_fn_insert a0 t0 f) a =
    dep_fn_insert a0 t0 (dep_fn_insert a1 t1 f) a.
  Proof.
    rewrite /dep_fn_insert => Hn.
    case: (decide _) => [|//]. intros ->.
    case: (decide _) => [|//] /=. by intros ->.
  Qed.

  (* Funext. *)

  Lemma dep_fn_insert_set_view_fun (f : ∀ a, T a) a0 :
    dep_fn_insert a0 (f a0) f = f.
  Proof. funext_dep => a. apply dep_fn_insert_set_view. Qed.

  Lemma dep_fn_insert_set_set_fun (f : ∀ a, T a) a0 (t1 t2 : T a0) :
    dep_fn_insert a0 t2 (dep_fn_insert a0 t1 f) =
    dep_fn_insert a0 t2 f.
  Proof. funext_dep => a. apply dep_fn_insert_set_set. Qed.

  Lemma dep_fn_insert_exchange_fun (f : ∀ a, T a) (a0 a1 : A) t0 t1 :
    a0 <> a1 ->
    dep_fn_insert a1 t1 (dep_fn_insert a0 t0 f) =
    dep_fn_insert a0 t0 (dep_fn_insert a1 t1 f) .
  Proof. intros Hn. funext_dep => a. exact: dep_fn_insert_exchange. Qed.
End dep_fn_insert.

Notation dep_fn_insert_eq := dep_fn_insert_view_set (only parsing).
Notation dep_fn_insert_ne := dep_fn_insert_view_set_ne (only parsing).
