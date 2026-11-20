(*
 * Copyright (C) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(** * Bit-fields: values and ownership

    A memory location (<https://eel.is/c++draft/intro.memory#3>) is either an
    object of scalar type or a maximal sequence of adjacent bit-fields of
    nonzero width, which we call a _run_ and name after its first named
    bit-field. cpp2v describes the supported bit-fields of each opaque record
    with [BitfieldInfo] (see [o_bitfields] in ../syntax/translation_unit.v).

    This file provides:
    - [bitfield.trunc] and [bitfield.in_range], the values of a bit-field;
    - [bitfieldsR], the ownership of one run, axiomatised without a model.

    There is deliberately no lemma changing the <<const>> flags of a
    [bitfieldsR], and no conversion to or from raw bytes, [anyR] or
    [tblockR]. Expressions on bit-fields are in [expr_bitfield.v]. *)
Require Import skylabs.prelude.base.
Require Import skylabs.prelude.arith.operator.
Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import skylabs.iris.extra.bi.fractional.
Require Import skylabs.iris.extra.bi.spec.frac_splittable.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.lang.cpp.logic.pred.
Require Import skylabs.lang.cpp.logic.heap_pred.

#[local] Open Scope Z_scope.

Module bitfield.

  (** [trunc s w v] is the value that a bit-field of width [w] and
      signedness [s] holds after storing [v]: [v] modulo [2^w], sign-extended
      if [s] is [Signed] (<https://eel.is/c++draft/conv.integral#3>, which
      Clang and GCC also follow before C++20). *)
  Definition trunc (s : signed) (w : N) (v : Z) : Z :=
    match s with
    | Signed => to_signed_bits w v
    | Unsigned => trim w v
    end.

  (** [in_range s w v] holds when [v] is a value of a bit-field of width [w]
      and signedness [s]. *)
  Definition in_range (s : signed) (w : N) (v : Z) : Prop :=
    match s with
    | Signed => - 2 ^ (Z.of_N w - 1) <= v < 2 ^ (Z.of_N w - 1)
    | Unsigned => 0 <= v < 2 ^ Z.of_N w
    end.

  #[global] Instance in_range_dec s w v : Decision (in_range s w v).
  Proof. destruct s; rewrite /in_range; apply _. Defined.

  Lemma trunc_in_range s w v : w <> 0%N -> in_range s w (trunc s w v).
  Proof.
    move=> Hw. have Hpos : 0 < 2 ^ Z.of_N w by apply Z.pow_pos_nonneg; lia.
    have Hhalf : 2 ^ Z.of_N w = 2 * 2 ^ (Z.of_N w - 1).
    { rewrite -Z.pow_succ_r; [f_equal|]; lia. }
    destruct s; rewrite /trunc /in_range.
    - rewrite /to_signed_bits bool_decide_eq_false_2 //; cbv zeta.
      have := Z.mod_pos_bound v (2 ^ Z.of_N w) Hpos.
      case_bool_decide; lia.
    - rewrite /trim. by apply Z.mod_pos_bound.
  Qed.

  Lemma trunc_id s w v : in_range s w v -> trunc s w v = v.
  Proof.
    destruct s; rewrite /trunc /in_range.
    - by move=> ?; apply to_signed_bits_spec_low.
    - by move=> ?; apply to_unsigned_bits_id.
  Qed.

  (** [wf tu cls run cs m] is what [bitfieldsR cls run q cs m] guarantees
      about its arguments, given the bit-field descriptions [tu] of the
      program: [m] only has values for fields in [cs], [cs] only has fields of
      the run [run] of [cls], and every value is in the range of its field. *)
  Definition wf (tu : translation_unit) (cls : globname) (run : ident)
      (cs : gmap ident bool) (m : gmap ident Z) : Prop :=
    dom m ⊆ dom cs /\
    (forall f, f ∈ dom cs ->
      exists info, bitfield_lookup tu cls f = Some info /\ info.(bf_run) = run) /\
    (forall f v, m !! f = Some v ->
      exists info, bitfield_lookup tu cls f = Some info /\
        in_range info.(bf_signed) info.(bf_width) v).

  (** The descriptions agree in compatible translation units: an opaque
      record is compatible only with itself (see [GlobDecl_le]). *)
  Lemma bitfield_lookup_sub_module tu1 tu2 cls f info :
    sub_module tu1 tu2 ->
    bitfield_lookup tu1 cls f = Some info ->
    bitfield_lookup tu2 cls f = Some info.
  Proof.
    rewrite /bitfield_lookup => Hsub.
    case Hl : (tu1.(types) !! cls) => [[]|] //.
    by rewrite (sub_module_preserves_gopaque _ _ _ _ Hsub Hl).
  Qed.

End bitfield.

(** ** Ownership of a run of bit-fields: axiomatised, without a model

    [bitfieldsR cls run q cs m] is fraction [q] of the memory location [run]
    of the object of class [cls] at the pointer it is placed at. Its fields
    are the keys of [cs], which maps each to whether it is <<const>>. [m]
    maps fields to their values; a field absent from [m] is indeterminate.

    Writes need the whole location ([q = 1]) and a non-<<const>> field; reads
    need the field's value in [m]. No lemma changes [cs]: constness is fixed
    for the lifetime of the Rep.

    NOTE: [bitfieldsR] has no model. Its properties are the axioms below,
    which are all it offers; keep them minimal. In particular nothing relates
    it to the bytes of the object, to [anyR] or to [tblockR], so objects with
    bit-fields can be neither created nor destroyed through it. *)
Parameter bitfieldsR : forall `{Σ : cpp_logic} {σ : genv}
  (cls : globname) (run : ident) (q : Qp) (cs : gmap ident bool) (m : gmap ident Z), Rep.
#[global] Arguments bitfieldsR {_ _ _ _} _%_cpp_name _%_pstring _%_Qp _ _ : assert.

Section bitfieldsR_axioms.
  Context `{Σ : cpp_logic} {σ : genv}.

  (** [bitfieldsR] is ownership: it is timeless, ... *)
  #[global] Declare Instance bitfieldsR_timeless cls run : Timeless3 (bitfieldsR cls run).

  (** ... it splits and combines by its fraction, for fixed [cs] and [m], ... *)
  #[global] Declare Instance bitfieldsR_fractional cls run : Fractional2 (bitfieldsR cls run).

  (** ... and its fraction is at most [1]. *)
  #[global] Declare Instance bitfieldsR_frac_valid cls run : FracValid2 (bitfieldsR cls run).

  (** Two fractions of a run agree on the <<const>> flags and the values. *)
  #[global] Declare Instance bitfieldsR_agree cls run q1 q2 cs1 cs2 m1 m2 :
    Observe2 [| cs1 = cs2 /\ m1 = m2 |]
      (bitfieldsR cls run q1 cs1 m1) (bitfieldsR cls run q2 cs2 m2).

  (** The fields and values agree with the descriptions of the program's
      bit-fields (see [bitfield.wf]). *)
  #[global] Declare Instance bitfieldsR_wf cls run q cs m :
    Observe [| bitfield.wf σ.(genv_tu) cls run cs m |] (bitfieldsR cls run q cs m).
End bitfieldsR_axioms.

(** ** Derived properties *)
Section bitfieldsR.
  Context `{Σ : cpp_logic} {σ : genv}.

  #[global] Instance bitfieldsR_as_fractional cls run q cs m :
    AsFractional (bitfieldsR cls run q cs m) (fun q => bitfieldsR cls run q cs m) q.
  Proof. constructor; [done|apply _]. Qed.

  #[global] Instance bitfieldsR_frac_splittable cls run :
    FracSplittable_2 (bitfieldsR cls run).
  Proof. solve_frac. Qed.

  #[global] Instance bitfieldsR_frac2_valid cls run q1 q2 cs1 cs2 m1 m2 :
    Observe2 [| q1 + q2 ≤ 1 |]%Qp
      (bitfieldsR cls run q1 cs1 m1) (bitfieldsR cls run q2 cs2 m2).
  Proof.
    iIntros "R1 R2".
    iDestruct (observe_2 [| _ /\ _ |] with "R1 R2") as %[Hcs Hm]; subst.
    iCombine "R1 R2" as "R". iApply (observe with "R").
  Qed.

  Lemma bitfieldsR_agree_at (p : ptr) cls run q1 q2 cs1 cs2 m1 m2 :
    p |-> bitfieldsR cls run q1 cs1 m1 ** p |-> bitfieldsR cls run q2 cs2 m2
    |-- [| cs1 = cs2 /\ m1 = m2 |].
  Proof. iIntros "[R1 R2]". iApply (observe_2 with "R1 R2"). Qed.

  Lemma bitfieldsR_wf_at (p : ptr) cls run q cs m :
    p |-> bitfieldsR cls run q cs m |-- [| bitfield.wf σ.(genv_tu) cls run cs m |].
  Proof. iIntros "R". iApply (observe with "R"). Qed.
End bitfieldsR.
