(*
 * Copyright (c) 2020-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.prelude.base.

#[local] Open Scope Z_scope.

(* Signed and Unsigned *)
Variant signed : Set := Signed | Unsigned.
#[global] Instance signed_eq_dec: EqDecision signed.
Proof. solve_decision. Defined.
#[global] Instance signed_countable : Countable signed.
Proof.
  apply (inj_countable'
           (λ s, if s is Signed then true else false)
           (λ b, if b then Signed else Unsigned)).
  abstract (by intros []).
Defined.

(* These take a bitsize in [N] *)
Definition bits_min_val (n : N) (sgn : signed) : Z :=
  match sgn with
  | Signed => -(2^(Z.of_N n - 1))
  | Unsigned => 0
  end.
Definition bits_max_val (n : N) (sgn : signed) : Z :=
  match sgn with
  | Signed => 2^(Z.of_N n-1) - 1
  | Unsigned => 2^(Z.of_N n) - 1
  end.
Definition bits_bound n sgn (z : Z) : Prop :=
  bits_min_val n sgn <= z <= bits_max_val n sgn.


(* Bit-widths *)
Module bitsize.
  Variant t : Set :=
  | W8
  | W16
  | W32
  | W64
  | W128.
  Notation bitsize := t.
  #[global] Instance bitsize_eq: EqDecision bitsize.
  Proof. solve_decision. Defined.
  #[global] Instance bitsize_countable : Countable bitsize.
  Proof.
    apply (inj_countable'
      (λ b,
        match b with
        | W8 => 0 | W16 => 1 | W32 => 2 | W64 => 3 | W128 => 4
        end)
      (λ n,
        match n with
        | 0 => W8 | 1 => W16 | 2 => W32 | 3 => W64 | 4 => W128
        | _ => W8	(* dummy *)
        end)).
    abstract (by intros []).
  Defined.

  Definition bitsN (s : bitsize) : N :=
    match s with
    | W8   => 8
    | W16  => 16
    | W32  => 32
    | W64  => 64
    | W128 => 128
    end.

  #[global] Instance bitsN_inj : Inj (=) (=) bitsN.
  Proof. red; intros x y H; by (destruct x; destruct y). Qed.

  Definition bitsZ (s : bitsize) : Z :=
    Z.of_N (bitsN s).

  Definition bytesNat (s : bitsize) : nat :=
    match s with
    | W8 => 1
    | W16 => 2
    | W32 => 4
    | W64 => 8
    | W128 => 16
    end.

  Definition bytesN (s : bitsize) : N :=
    N.of_nat (bytesNat s).

  Definition bytesZ (s : bitsize) : Z :=
    Z.of_N (bytesN s).

  Definition max_val (bits : bitsize) (sgn : signed) : Z :=
    bits_max_val (bitsN bits) sgn.

  Definition min_val (bits : bitsize) (sgn : signed) : Z :=
    bits_min_val (bitsN bits) sgn.

  Definition bound (bits : bitsize) (sgn : signed) (v : Z) : Prop :=
    min_val bits sgn <= v <= max_val bits sgn.

End bitsize.
Notation bitsize := bitsize.t.
#[global] Arguments N.of_nat !_ /.
#[global] Arguments bitsize.bytesN !_ /.
#[global] Arguments bitsize.bytesZ !_ /.

Bind Scope N_scope with bitsize.

Lemma of_size_gt_O w :
  (0 < 2 ^ bitsize.bitsZ w)%Z.
Proof. destruct w; reflexivity. Qed.
(* Hint Resolve of_size_gt_O. *)

Lemma bytesZ_positive s :
  (0 < bitsize.bytesZ s)%Z.
Proof. destruct s; reflexivity. Qed.

Lemma bytesZ_range s : (0 < bitsize.bytesZ s < 17)%Z.
Proof. destruct s; cbn; lia. Qed.

Variant endian : Set := Little | Big.
#[global] Instance endian_dec : EqDecision endian.
Proof. solve_decision. Defined.
