(*
 * Copyright (c) 2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.prelude.base.
Require Stdlib.Numbers.BinNums.
Require Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Stdlib.micromega.ZifyUint63.

#[local] Open Scope Z_scope.

#[global] Arguments Uint63.to_Z : simpl nomatch.

Module Uint63.
  Export Uint63.

  Notation max_intZ := 9223372036854775807%Z.
  Notation sup_intZ := 9223372036854775808%Z.

  (** Returns a sequence of [n] integers, from [start] to [start + n - 1] (up to conversions). *)
  Fixpoint seq_int (start : int) (n : nat) : list int :=
    match n with
    | 0 => []
    | S n => start :: seq_int (Uint63.succ start) n
    end%nat.

  Lemma seq_int_length start n : List.length (seq_int start n) = n.
  Proof.
    elim: n start => [|n IHn] start //.
    by rewrite /= IHn.
  Qed.

  Lemma seq_int_nth start n k d :
    nth k (seq_int start n) d =
      if decide (k < n) then
        (start + of_Z k)%uint63
      else
        d.
  Proof.
    elim: n start k d => [|n IHn] start k d //.
    - case_decide => //.
      + lia.
      + rewrite nth_overflow // seq_int_length. lia.
    - case: k.
      + cbn; case_decide; lia.
      + intros. cbn. rewrite {}IHn.
        repeat case_decide; [..|lia|lia|reflexivity]. lia.
  Qed.

  #[global] Instance Uint63_EqDec : EqDecision Uint63.int := Uint63.eqs.
  #[global, program] Instance Uint63_Coountable : Countable Uint63.int :=
    {
      encode i := Z.to_pos (1 + (Uint63.to_Z i))%Z;
      decode p := Some (Uint63.of_Z (Z.pos p - 1)%Z)
    }.
  Next Obligation. intros. simpl. f_equal. rewrite -[x in _ = x]of_to_Z. lia. Qed.

  Definition compare_spec_Z x y :
    CompareSpec (x = y) (to_Z x < to_Z y) (to_Z x > to_Z y) (x ?= y)%uint63.
  Proof.
    rewrite Uint63.compare_spec. case: Z.compare_spec; constructor; lia.
  Qed.
End Uint63.
