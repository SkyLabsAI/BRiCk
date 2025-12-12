(*
 * Copyright (c) 2021-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.prelude.base.
Require Import bluerock.prelude.bool.
Require Import bluerock.prelude.finite.
Require Import bluerock.prelude.fin.
Require Import bluerock.prelude.list_numbers.
#[local] Set Printing Coercions.

(** [get_range_bitsN] *)
(**
Extract from [val] the [count] lowest bits starting from [from].
Follows [get_range_bits] but on [N].

TODO: this one generalizes bluerock.prelude.arith.builtins._get_byte. Consider
unifying them.
*)
Definition get_range_bitsN (val from count : N) : N :=
  N.land (val ≫ from) (N.ones count).

Section get_range_bitsN.
  #[local] Open Scope N_scope.

  Lemma get_range_bitsN_eq val from count :
    get_range_bitsN val from count = (val ≫ from) `mod` 2 ^ count.
  Proof. by rewrite /get_range_bitsN N.land_ones. Qed.

  Lemma get_range_bitsN_1_eq val from :
    get_range_bitsN val from 1 = N.b2n (N.testbit val from).
  Proof.
    rewrite get_range_bitsN_eq N.testbit_eqb -N.shiftr_div_pow2.
    case: N.eqb_spec =>//.
    move: (N.shiftr _ _) => {val from} x.
    have /= := N.mod_upper_bound x 2.
    move: (N.modulo _ _).
    lia.
  Qed.

  Lemma get_range_bitsN_1_bool_decide_eq val from :
    bool_decide (get_range_bitsN val from 1 = 1) = N.testbit val from.
  Proof.
    rewrite get_range_bitsN_1_eq.
    by rewrite (bool_decide_ext _ _ (N_b2n_1 _)) bool_decide_Is_true.
  Qed.

  Lemma get_range_bitsN_bounded {n i cnt : N} :
    get_range_bitsN n i cnt < 2^cnt.
  Proof.
    rewrite get_range_bitsN_eq. apply N.mod_bound_pos. { apply N.le_0_l. }
    by apply N.le_succ_l, (N.pow_le_mono_r 2 0), N.le_0_l.
  Qed.

  Definition get_range_bits_fin (val from count : N) : fin.t (2 ^ count) :=
    fin.mk (get_range_bitsN val from count) get_range_bitsN_bounded.

  Section get_range_bitsN_bounded_elim.
    Context {X} (of_N : N -> option X) (count : N) {n from : N}.

    Lemma get_range_bitsN_bounded_elim
      (Hdef : ∀ n, n < 2 ^ count → of_N n ≠ None) :
      is_Some (of_N (get_range_bitsN n from count)).
    Proof. apply not_eq_None_Some, Hdef, get_range_bitsN_bounded. Qed.

    Lemma get_range_bitsN_bounded_elim'
      (Hdef : List.Forall (λ i , of_N i ≠ None) (seqN 0 (2 ^ count))) :
      is_Some (of_N (get_range_bitsN n from count)).
    Proof. apply get_range_bitsN_bounded_elim, N_fin_iter_lt, Hdef. Qed.
  End get_range_bitsN_bounded_elim.
End get_range_bitsN.
