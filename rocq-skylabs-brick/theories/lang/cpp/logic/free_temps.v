(*
 * Copyright (c) 2020-2026 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.

Require Import skylabs.lang.cpp.syntax.types.
Require Import skylabs.lang.cpp.semantics.ptrs.

Declare Scope free_scope.
Delimit Scope free_scope with free.
Reserved Infix "|*|" (at level 30).
Reserved Infix ">*>" (at level 30).

Module FreeTemps.

  (* BEGIN FreeTemps.t *)
  Inductive t : Set :=
  | id (* = fun x => x *)
  | delete (ty : decltype) (p : ptr) (* = delete_val ty p *)
           (* ^^ this type has qualifiers but is otherwise a runtime type *)
  | delete_va (va : list (type * ptr)) (p : ptr)
  | seq (f g : t) (* = fun x => f $ g x *)
  | par (f g : t) (* = fun x => Exists Qf Qg, f Qf ** g Qg ** (Qf -* Qg -* x) *)
  .
  (* END FreeTemps.t *)

  Module Import notations.
    Bind Scope free_scope with t.
    Notation "1" := id : free_scope.
    Infix ">*>" := seq : free_scope.
    Infix "|*|" := par : free_scope.
  End notations.
  #[local] Open Scope free_scope.

  Inductive t_equiv : Equiv t :=
  | refl l : l ≡ l
  | sym l r : l ≡ r -> r ≡ l
  | trans a b c : a ≡ b -> b ≡ c -> a ≡ c

  | delete_ref ty p : delete (Tref ty) p ≡ delete (Trv_ref ty) p

  | seqA x y z : x >*> (y >*> z) ≡ (x >*> y) >*> z
  | seq_id_unitL l : 1 >*> l ≡ l
  | seq_id_unitR l : l >*> 1 ≡ l
  | seq_proper_ : ∀ {a b}, a ≡ b -> ∀ {c d}, c ≡ d -> a >*> c ≡ b >*> d

  | parC l r : l |*| r ≡ r |*| l
  | parA x y z : x |*| (y |*| z) ≡ (x |*| y) |*| z
  | par_id_unitL l : 1 |*| l ≡ l
  | par_proper_ : ∀ {a b}, a ≡ b -> ∀ {c d}, c ≡ d -> a |*| c ≡ b |*| d
  .
  Notation t_eq := (≡@{t}) (only parsing).

  #[global] Existing Instance t_equiv.
  #[global] Instance t_equivalence : Equivalence t_eq :=
    Build_Equivalence _ refl sym trans.

  #[global] Instance seq_assoc : Assoc equiv seq := seqA.
  #[global] Instance seq_left_id : LeftId equiv id seq := seq_id_unitL.
  #[global] Instance seq_right_id : RightId equiv id seq := seq_id_unitR.
  #[global] Instance seq_proper : Proper (t_eq ==> t_eq ==> t_eq) seq := @seq_proper_.

  #[global] Instance par_comm : Comm equiv par := parC.
  #[global] Instance par_left_id : LeftId equiv id par := par_id_unitL.
  #[global] Instance par_right_id : RightId equiv id par.
  Proof. intros x. by rewrite comm left_id. Qed.
  #[global] Instance par_proper : Proper (t_eq ==> t_eq ==> t_eq) par := @par_proper_.

  (**
  [pars ls] is the [FreeTemp] representing the destruction of each
  element in [ls] *in non-deterministic order*.
  *)
  Definition pars : list t -> t := foldr par 1.

  (**
  [seqs ls] is the [FreeTemp] representing the destruction of each
  element in [ls] sequentially from left-to-right, i.e. the first
  element in the list is run first.
  *)
  Definition seqs : list t -> t := foldr seq 1.

  (**
  [seqs_rev ls] is the [FreeTemp] representing the destruction of each
  element in [ls] sequentially from right-to-left, i.e. the first
  element in the list is destructed last.
  *)
  Definition seqs_rev : list t -> t := foldl (fun a b => seq b a) 1.
End FreeTemps.
Export FreeTemps.notations.
Notation FreeTemps := FreeTemps.t.
Notation FreeTemp := FreeTemps.t (only parsing).
