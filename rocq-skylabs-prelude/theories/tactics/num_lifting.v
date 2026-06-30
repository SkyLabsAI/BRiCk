(*
 * Copyright (C) 2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** * This file defines the tactic [lift_NtoZ]

    [lift_NtoZ] is used in combination with a database of rewriting rules to lift lemmas from type
    [N] to type [Z] -- in particular when they are used by list functions as is done in
    [skylabs.prelude.list_numbers].
    
    TODO: extend documentation.
 *)
Require Import stdpp.prelude.

Require Import Ltac2.Ltac2.
Require Import Ltac2.Rewrite.

#[local] Coercion Z.of_N : N >-> Z.

Module internals.
  Import Strategy Printf.

  #[local] Open Scope Z_scope.

  Lemma port_forall_to_Z (P : N -> Prop) : (forall x : N, P x) <-> (forall x : Z, P (Z.to_N x)).
  Proof. Admitted.
  Lemma port_eq_N (x y : N) : (x = y) <-> (Z.of_N x) = (Z.of_N y).
  Proof. Admitted.

  (* This lemma is written with [impl] instead of an arrow so that the implication will be
     considered as a rewriting relation. *)
  Lemma port_Nle_ZtoN (i : Z) (n : N) : impl (Z.of_N n ≤ i) (n ≤ Z.to_N i)%N.
  Proof. unfold impl; ltac1:(lia). Qed.

  Lemma port_ZtoN_Nle (i : Z) (n : N) : (Z.to_N i ≤ n)%N <-> i ≤ Z.of_N n.
  Proof. ltac1:(lia). Qed.

  Lemma port_Nle (m n : N) : (m ≤ n)%N <-> m ≤ n.
  Proof. ltac1:(lia). Qed.

  Lemma port_Z2N_add_total (m n : Z) : (Z.to_N m + Z.to_N n)%N = Z.to_N (m `max` 0 + n `max` 0).
  Proof. ltac1:(lia). Qed.

  #[global] Create Rewrite HintDb lift_NtoZ.

  #[global] Hint Rewrite @port_eq_N : lift_NtoZ.

  (* arithmetic *)
  #[global] Hint Rewrite @N2Z.inj_min : lift_NtoZ.
  #[global] Hint Rewrite @N2Z.inj_max : lift_NtoZ.
  #[global] Hint Rewrite @N2Z.inj_sub_max : lift_NtoZ.
  #[global] Hint Rewrite @N2Z.inj_add : lift_NtoZ.
  #[global] Hint Rewrite @N2Z.inj_mul : lift_NtoZ.
  #[global] Hint Rewrite @N2Z.inj_div : lift_NtoZ.
  #[global] Hint Rewrite @N2Z.inj_succ : lift_NtoZ.
  #[global] Hint Rewrite <- @Z.add_1_r : lift_NtoZ.

  #[global] Hint Rewrite port_Z2N_add_total : lift_NtoZ.

  (* comparison *)
(*      NOTE: the order in which the hints are registered matters *)
  #[global] Hint Rewrite @port_Nle : lift_NtoZ.
  #[global] Hint Rewrite @port_ZtoN_Nle : lift_NtoZ.
  #[global] Hint Rewrite <- @port_Nle_ZtoN : lift_NtoZ.

  (* numerals *)
  #[global] Hint Rewrite @N2Z.inj_0 : lift_NtoZ.
  #[global] Hint Rewrite @N2Z.inj_pos : lift_NtoZ.

  Ltac2 rewrite_N_to_Z hyp : unit :=
    let rw_all := terms [preterm:(@port_forall_to_Z)] in
    let hints := choices [hints @lift_NtoZ; old_hints (@lift_NtoZ)] in
    let strat_forall := outermost rw_all in
    let strat_port   := try (topdown hints) in
    (* [rewrite_strat] fails to create a [Proper] instance after rewriting quantifiers so we need to
       use it with [repeat] *)
    Notations.repeat (rewrite_strat strat_forall hyp) ;
    rewrite_strat strat_port hyp.

  Ltac2 lift_NtoZ (id : ident) (lmm : constr) : unit :=
    Std.assert (Std.AssertValue id lmm) ;
    rewrite_N_to_Z (Some id) ;
    ().

  Ltac2 Notation "lift_NtoZ" id(ident) ":=" lmm(constr) := lift_NtoZ id lmm.

  Ltac2 ltac1_lift_NtoZ id lmm :=
    let id := Option.get (Ltac1.to_ident id) in
    let lmm := Option.get (Ltac1.to_constr lmm) in
    lift_NtoZ $id := $lmm.

  Ltac2 ltac1_rewrite_NtoZ () :=
    rewrite_N_to_Z None.

  Ltac2 ltac1_rewrite_NtoZ_in id :=
    let id := Option.get (Ltac1.to_ident id) in
    rewrite_N_to_Z (Some id).

End internals.

Tactic Notation (at level 5) "lift_NtoZ" "(" ident(id) ":=" constr(lmm) ")" :=
  let tac := ltac2:(id lmm |- internals.ltac1_lift_NtoZ id lmm) in
  tac id lmm.

Tactic Notation "lift_NtoZ" "in" ident(id) :=
  let tac := ltac2:(id |- internals.ltac1_rewrite_NtoZ_in id) in
  tac id.

Tactic Notation "lift_NtoZ" :=
  ltac2:(internals.ltac1_rewrite_NtoZ ()).
