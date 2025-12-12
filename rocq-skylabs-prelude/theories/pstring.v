(*
 * Copyright (c) 2024-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import Stdlib.Strings.PString.

(* We have to undo a bunch of things. But we only want to to override mutable
   ltac if the current values are exactly as we think they are. *)
Goal exists b:bool, b = true.
Proof.
  exists ltac:(let t := ltac:(Zify.zify_convert_to_euclidean_division_equations_flag) in exact t).
  reflexivity.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module Tmp.
  Inductive tmp := Tmp.
  #[local] Ltac ZifyBool.elim_bool_cstr ::= exact Tmp.

  Goal tmp.
    Zify.zify_post_hook.
  Qed.
End Tmp.
Ltac Zify.zify_post_hook ::= idtac.

Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Import stdpp.numbers.
Require Import stdpp.relations.
Require Import stdpp.countable.
Require Import stdpp.finite.
Require Import bluerock.prelude.base.

Export PrimString.PStringNotations.

Infix "++" := PrimString.cat : pstring_scope.

Definition join_sep {A : Type} (sep : A) : forall (ls : list A), list A :=
  (fix go acc ls {struct ls} :=
    match ls with
    | [] => []
    | x :: ls => acc ++ x :: go [sep] ls
    end
  ) [].

Definition concat_sep {A : Type} (sep : A) : forall (ls : list (list A)), list A :=
  (fix go acc ls {struct ls} :=
    match ls with
    | [] => []
    | x :: ls => acc ++ x ++ go [sep] ls
    end
  ) [].

Definition foldi {A:Type} (f : forall (ind_nat : nat) (ind_int : int) (acc : A), A) (ps : string) :
  forall (acc : A), A :=
  let len := Z.to_nat $ to_Z $ PrimString.length ps in
  (fix go l n i a : A :=
     match l with
     | S l => f n i (go l (S n) (i + 1)%uint63 a)
     | 0 => a
     end
  ) len 0 0%uint63.

(* TODO: this is horribly inefficient and is only here for API compatibility
   with bytestrings. *)
Module Buf.
  Inductive t : Set :=
  | Empty
  | Byte (_ : char63)
  | String (_ : string)
  | Append (_ _ : t)
  | Concat (_ : t) (_ : list t).

  Definition concat_aux (contents_aux : t -> string -> string) (sep : t) :=
    fix concat_aux (l : list t) (acc : string) : string :=
    match l with
    | nil => acc
    | b :: nil => contents_aux b acc
    | b :: (_ :: _) as l =>
      let acc := concat_aux l acc in
      let acc := contents_aux sep acc in
      contents_aux b acc
    end.
  Fixpoint contents_aux (b : t) (acc : string) {struct b} : string :=
    match b with
    | Empty => acc
    | Byte b => PrimString.cat (PrimString.make 1 b) acc
    | String s => PrimString.cat s acc
    | Append b1 b2 =>
      let acc := contents_aux b2 acc in
      contents_aux b1 acc
    | Concat sep bufs => concat_aux contents_aux sep bufs acc
    end.
  Definition contents (b : t) : string := contents_aux b "".

  #[global] Instance empty : base.Empty t := Empty.
  #[global] Instance monoid : monoid.Monoid t := {
    monoid.monoid_unit := Empty;
    monoid.monoid_op := Append;
  }.
End Buf.

Fixpoint concat (ls : list string) : string :=
  match ls with
  | [] => ""
  | x :: ls => PrimString.cat x (concat ls)
  end.

Definition is_space (x : PrimString.char63) :=
  (  (x =? 011)
  || (x =? 013)
  || (x =? 009)
  || (x =? 010)
  || (x =? 012)
  || (x =? " ".(char63_wrap))
  )%uint63%char63.

Definition in_range_incl : forall (s : char63) (e : char63) (c : char63), bool :=
  fun s e c => ((s <=? c) && (c <=? e))%uint63.

Definition in_range_excl : forall (s : char63) (e : char63) (c : char63), bool :=
  fun s e c => ((s <? c) && (c <? e))%uint63.

Definition in_range_excl_incl : forall (s : char63) (e : char63) (c : char63), bool :=
  fun s e c => ((s <? c) && (c <=? e))%uint63.

Definition in_range_incl_excl : forall (s : char63) (e : char63) (c : char63), bool :=
  fun s e c => ((s <=? c) && (c <? e))%uint63.

#[global,program]
Instance eqdec_char63 : EqDecision char63 := fun c1 c2 =>
  match PrimInt63.eqb c1 c2 as c return PrimInt63.eqb c1 c2 = c -> _ with
  | true => fun _ => left _
  | false => fun _ => right _
  end eq_refl.
Next Obligation.
  intros c1 c2 Hcmp. apply Uint63.eqb_correct. exact Hcmp.
Qed.
Next Obligation.
  intros c1 c2 Hcmp H. rewrite H in Hcmp.
  rewrite Uint63.eqb_refl in Hcmp. inversion Hcmp.
Qed.

#[global, program]
Instance eqdec_pstring : EqDecision string := fun i1 i2 =>
  match PrimString.compare i1 i2 as c return PrimString.compare i1 i2 = c -> _ with
  | Eq => fun _ => left _
  | _  => fun _ => right _
  end eq_refl.
Next Obligation.
  apply compare_eq_correct.
Qed.
Next Obligation.
  intros ? ? Hcmp H.
  rewrite H compare_refl in Hcmp. inversion Hcmp.
Qed.
Next Obligation.
  intros ? ? Hcmp H.
  rewrite H compare_refl in Hcmp. inversion Hcmp.
Qed.

Definition pstring_eqb (x y : string) : bool := bool_decide (x = y).

#[global] Instance string_inhabited : Inhabited string.
Proof. constructor. exact ""%pstring. Defined.

#[global] Instance char63_countable : Countable char63 :=
  inj_countable' to_Z of_Z of_to_Z.

#[global] Instance string_countable : Countable string :=
  inj_countable' to_list of_list of_to_list.

Definition index (needle: PrimString.string) (haystack: PrimString.string) : option int :=
  if bool_decide (needle = ""%pstring) then
    if bool_decide (haystack = ""%pstring) then
      Some 0%uint63
    else
      None
  else
  let nlen := PrimString.length needle in
  let hlen := PrimString.length haystack in
  let len := Z.to_nat $ to_Z hlen in
  (fix go l i : option int :=
     match l with
     | S l =>
         if bool_decide (nlen <=? hlen - i)%uint63 then
           if PrimString.compare (PrimString.sub haystack i nlen) needle is Eq then
             Some i
           else
             go l (i + 1)%uint63
         else
           go l (i + 1)%uint63
     | 0 => None
     end
  ) len 0%uint63.

Definition contains needle haystack :=
  if index needle haystack is Some _ then true else false.


(* Module strongly inspired from [stdpp.pretty]. *)
Module N.
  #[local] Open Scope N_scope.

  Definition to_string_digit (n : N) : string :=
    match n with
    | 0 => "0"%pstring
    | 1 => "1"%pstring
    | 2 => "2"%pstring
    | 3 => "3"%pstring
    | 4 => "4"%pstring
    | 5 => "5"%pstring
    | 6 => "6"%pstring
    | 7 => "7"%pstring
    | 8 => "8"%pstring
    | _ => "9"%pstring
    end.

  Fixpoint to_string_aux (n : N) (acc : Acc (<)%N n) (s : string) : string :=
    match decide (0 < n) with
    | left H =>
        to_string_aux (n `div` 10)
          (Acc_inv acc (N.div_lt n 10 H eq_refl))
          (cat (to_string_digit (n `mod` 10)) s)
    | right _ => s
    end.

  Definition to_string (n : N) : string :=
    match n with
    | N0 => "0"%pstring
    | _  => to_string_aux n (wf_guard (S (N.size_nat n)) N.lt_wf_0 n) ""%pstring
    end.
End N.
