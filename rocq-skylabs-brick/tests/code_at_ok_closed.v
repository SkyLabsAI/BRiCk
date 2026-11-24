(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.lang.cpp.logic.
Require Import skylabs.iris.extra.bi.errors.
Require Import iris.proofmode.proofmode.

(** [code_at] is closed under [ObjValue_ler]. [code_at_ok] stays sound if,
    for every [f ≤ f'], the semantics of [f] refines that of [f'] and both
    have the same type: the axiom for the loaded record [f'] then covers [f].
 *)

#[local] Ltac split_bool :=
  repeat match goal with
         | H : context [bool_decide ?P] |- _ =>
             destruct (bool_decide_reflect P); cbn in H; try discriminate
         | H : _ /\ _ |- _ => destruct H
         end; subst.

(** ** Types *)

Lemma type_of_value_func_ler f f' :
  ObjValue_ler (Ofunction f) (Ofunction f') ->
  f.(f_body) <> None ->
  type_of_value (Ofunction f) = type_of_value (Ofunction f').
Proof.
  destruct f as [r ps cc ar ex att [b|]], f' as [r' ps' cc' ar' ex' att' [b'|]];
    rewrite /= => H Hb //; split_bool; done.
Qed.

Lemma type_of_value_method_ler m m' :
  ObjValue_ler (Omethod m) (Omethod m') ->
  m.(m_body) <> None ->
  type_of_value (Omethod m) = type_of_value (Omethod m').
Proof.
  destruct m as [r cls q ps cc ar ex att [b|]], m' as [r' cls' q' ps' cc' ar' ex' att' [b'|]];
    rewrite /= => H Hb //; split_bool; done.
Qed.

Lemma type_of_value_ctor_ler c c' :
  ObjValue_ler (Oconstructor c) (Oconstructor c') ->
  c.(c_body) <> None ->
  type_of_value (Oconstructor c) = type_of_value (Oconstructor c').
Proof.
  destruct c as [cls ps cc ar ex [b|]], c' as [cls' ps' cc' ar' ex' [b'|]];
    rewrite /= => H Hb //; split_bool; done.
Qed.

Lemma type_of_value_dtor_ler d d' :
  ObjValue_ler (Odestructor d) (Odestructor d') ->
  type_of_value (Odestructor d) = type_of_value (Odestructor d').
Proof.
  destruct d as [cls cc ex b], d' as [cls' cc' ex' b'];
    rewrite /= => H; split_bool; done.
Qed.

Section refine.
  Context `{Σ : cpp_logic, σ : genv}.

  (** ** Functions: [f'] may differ from a concrete [f] only in [f_exception],
      which [wp_func] does not read. *)
  Lemma wp_func_ler tu f f' ls Q :
    ObjValue_ler (Ofunction f) (Ofunction f') ->
    wp_func tu f ls Q |-- wp_func tu f' ls Q.
  Proof.
    rewrite wp_func.unlock.
    destruct f as [r ps cc ar ex att [b|]], f' as [r' ps' cc' ar' ex' att' [b'|]];
      rewrite /= => H; split_bool; try done.
    all: by rewrite ERROR_elim'.
  Qed.

  (** ** Methods: [Defaulted ≤ CompilerProvided b] is the only slack. A
      [Defaulted] method is [UNSUPPORTED] unless it is a union's copy or move
      assignment, and then [wp_method] ignores [b]: both sides copy bytes. *)
  Lemma wp_method_ler tu m m' ls Q :
    ObjValue_ler (Omethod m) (Omethod m') ->
    wp_method tu m ls Q |-- wp_method tu m' ls Q.
  Proof.
    rewrite wp_method.unlock.
    destruct m as [r cls q ps cc ar ex att [[|b|b]|]],
             m' as [r' cls' q' ps' cc' ar' ex' att' [[|b'|b']|]];
      rewrite /OrDefault_le /= => H; split_bool; try done.
    all: try by rewrite ERROR_elim'.
    destruct ls as [|? [|? [|]]]; try exact: UNSUPPORTED_elim'.
    destruct (_ !! _) as [[]|]; try exact: UNSUPPORTED_elim'; done.
  Qed.

  (** ** Constructors: as for methods. *)
  Lemma wp_ctor_ler tu c c' ls Q :
    ObjValue_ler (Oconstructor c) (Oconstructor c') ->
    wp_ctor tu c ls Q |-- wp_ctor tu c' ls Q.
  Proof.
    rewrite wp_ctor.unlock.
    destruct c as [cls ps cc ar ex [[|b|b]|]],
             c' as [cls' ps' cc' ar' ex' [[|b'|b']|]];
      rewrite /OrDefault_le /= => H; split_bool; try done.
    all: try by rewrite ERROR_elim'.
    destruct ls as [|? [|? [|]]]; try exact: UNSUPPORTED_elim'.
    destruct (_ !! _) as [[]|]; try exact: UNSUPPORTED_elim'; done.
  Qed.

  (** ** Destructors: [Defaulted ≤ CompilerProvided (Sseq [])] (see
      [DtorBody_le]); the empty block takes one more step than [Defaulted]. *)
  Lemma wp_dtor_ler tu d d' ls Q :
    ObjValue_ler (Odestructor d) (Odestructor d') ->
    wp_dtor tu d ls Q |-- wp_dtor tu d' ls Q.
  Proof.
    rewrite wp_dtor.unlock.
    destruct d as [cls cc ex [[|b|b]|]],
             d' as [cls' cc' ex' [[|b'|b']|]];
      rewrite /DtorBody_le /OrDefault_le /= => H; split_bool; try done.
    all: try by rewrite ERROR_elim'.
    (* [Defaulted] below [CompilerProvided (Sseq [])] *)
    repeat case_match; try done.
    all: iIntros "wp !>"; iRevert "wp".
    all: rewrite -wp_seq wp_block_unfold.
    all: iIntros ">wp !> !> !>"; iExact "wp".
  Qed.
End refine.

(** ** [code_at_ok] for the closed [code_at]

    Abstractly: if [code_at] is the [ObjValue_ler]-closure of some [E], and
    the compiler axiom holds for the exact records [E], it holds for
    [code_at]. In [simple_pred], [E f p] is [code_own p (inl (inl (inl f)))].
 *)
Section code_at_ok_closed.
  Context `{Σ : cpp_logic, σ : genv}.

  Context (E : Func -> ptr -> mpred).
  Context (code_at_closure : forall f p,
    code_at f p -|- Exists f', [| ObjValue_ler (Ofunction f) (Ofunction f') |] ** E f' p).
  Context (exact_ok : forall tu, tu ⊧ σ -> forall f p,
    E f p |-- Forall ls Q, wp_func tu f ls Q -*
                           wp_fptr (type_of_value (Ofunction f)) p ls Q).

  Lemma code_at_ok_closed tu : tu ⊧ σ -> forall f p,
    code_at f p
    |-- Forall ls Q, wp_func tu f ls Q -*
                     wp_fptr (type_of_value (Ofunction f)) p ls Q.
  Proof using All.
    intros Htu f p. rewrite code_at_closure. iDestruct 1 as (f' Hle) "E". iIntros (ls Q) "wp".
    destruct (decide (f.(f_body) = None)) as [Hb|Hb].
    { rewrite wp_func.unlock. destruct f as [??????[]]; cbn in Hb; try done.
      cbn. by iDestruct (ERROR_elim with "wp") as "[]". }
    rewrite (type_of_value_func_ler _ _ Hle Hb).
    iApply (exact_ok _ Htu with "E"). by iApply wp_func_ler.
  Qed.
End code_at_ok_closed.
