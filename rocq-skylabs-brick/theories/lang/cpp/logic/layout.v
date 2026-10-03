(*
 * Copyright (c) 2020-2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Import skylabs.prelude.numbers.
Require Import skylabs.prelude.list.
Require Import skylabs.iris.extra.proofmode.proofmode.

Require Import skylabs.prelude.arith.z_to_bytes.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.logic.pred.
Require Import skylabs.lang.cpp.logic.path_pred.
Require Import skylabs.lang.cpp.logic.heap_pred.
Require Import skylabs.lang.cpp.logic.translation_unit.
Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.lang.cpp.logic.arr.
Require Export skylabs.lang.cpp.logic.raw.

Require Import skylabs.iris.extra.bi.linearity.

Section with_Σ.
  Context `{Σ : cpp_logic} {σ : genv}.

  (* Convert a <<struct>> to its raw representation.
  Justified by the concept of object representation.
  https://eel.is/c++draft/basic.types.general#def:representation,object

  DISABLED as unused and unsound. Take this code:
  <<
    struct E { };                  // POD, size_of = 1, occupies 0 bytes as a base
    struct D : E { unsigned char c; };   // standard-layout, size_of = 1, [c] at offset 0
  >>
  [sizeof(E) = 1], but [E] subobjects in [D] complete objects occupy 0 bytes.

  We end up with both the base class and [D]'s first field claiming to own the first raw byte,
  so, if we enable [eval_o_base] (which holds in models), we can prove
  <<
  structR "E" q |-- Exists r : raw_byte, rawR q r.

  offset_cong σ (o_base σ "D" "E") (o_field σ "D::c").

  p ,, o_base σ "D" "E" |-> structR "E" 1$m **
  p ,, o_field σ "D::c" |-> anyR Tbyte 1$m
  |-- False.

  p |-> anyR "D" 1$m |-- False.
  >>

  See https://github.com/SkyLabsAI/BRiCk/issues/310 for the follow-up work.
  *)
  (*
  Axiom struct_to_raw : forall cls st rss q,
    glob_def σ cls = Some (Gstruct st) ->
    st.(s_layout) ∈ [POD;Standard] ->
       structR cls q **
       ([∗ list] b ∈ st.(s_bases),
          Exists rs, [| rss !! FieldOrBase.Base b.1 = Some rs |] ** _base cls b.1 |-> rawsR q rs) **
       ([∗ list] fld ∈ st.(s_fields),
          Exists rs, [| rss !! FieldOrBase.Field fld.(mem_name) = Some rs |] **
            _field (Field cls fld.(mem_name)) |-> rawsR q rs)
    -|- type_ptrR (Tnamed cls) **
      Exists rs, rawsR q rs ** [| raw_bytes_of_struct σ cls rss rs |].
   *)

  #[local] Definition implicit_destruct_ty (ty : type) :=
    anyR ty 1$m |-- |={↑pred_ns}=> tblockR ty 1$m.

  (** implicit destruction of a primitive *)
  Axiom implicit_destruct_int : forall sz sgn, Reduce (implicit_destruct_ty (Tnum sz sgn)).
  Axiom implicit_destruct_bool : Reduce (implicit_destruct_ty Tbool).
  Axiom implicit_destruct_nullptr : Reduce (implicit_destruct_ty Tnullptr).
  Axiom implicit_destruct_ptr : forall ty, Reduce (implicit_destruct_ty (Tptr ty)).
  Axiom implicit_destruct_member_pointer : forall cls ty, Reduce (implicit_destruct_ty (Tmember_pointer cls ty)).
  (** ^^ TODO: the above axioms need to be lowered or proven. They are not provable
      now because we can not decompose [tptsto ty q Vundef] (which is what we
      get from [anyR]). *)

  (** implicit destruction of an aggregate.
  XXX: Incompatible with [eval_o_base]. *)
  (* Axiom implicit_destruct_struct
  : forall cls st q,
      glob_def σ cls = Some (Gstruct st) ->
      st.(s_trivially_destructible) ->
      cQp.frac q = 1%Qp ->
          type_ptrR (Tnamed cls)
      |-- (Reduce (struct_defR tblockR cls st q)) -*
          |={↑pred_ns}=> tblockR (Tnamed cls) q.

  (** implicit destruction of a union. *)
  Axiom implicit_destruct_union : forall (cls : globname) un q,
      glob_def σ cls = Some (Gunion un) ->
      un.(u_trivially_destructible) ->
      cQp.frac q = 1%Qp ->
          type_ptrR (Tnamed cls)
      |-- (Reduce (union_defR tblockR cls un q)) -* |={↑pred_ns}=> tblockR (Tnamed cls) q. *)

(*
  (* the following rule would allow you to change the active entity in a union
     using only ghost code. The C++ semantics does not permit this, rather
     it requires this to happen in code, so we will need to fuse this rule into
     the assignment rule.

     NOTE the axiom requires that the union element has been destructed
          (which will often be done implicitly), and the result gives you
          uninitialized memory ([tblockR]).

     NOTE C++ would permit this rule to be slightly stronger than stated here, because C++ guarantees
          that if two fields have common prefixes, that those values are preserved
          across this operation.
   *)
  Axiom union_change
  : forall (cls : globname) un,
      glob_def resolve cls = Some (Gunion un) ->
(*      un.(u_trivially_destructible) -> *)
      type_ptrR (Tnamed cls)
      |-- (union_def (fun ty => tblockR ty 1$m) cls un)
      -* [∧ list] idx ↦ it ∈ un.(u_fields),
          let f := _field {| f_name := it.(mem_name) ; f_type := cls |} in
          |={↑pred_ns}=> f |-> tblockR (erase_qualifiers it.(mem_type)) 1$m **
               unionR cls 1$m (Some idx).
*)

  (** Empty arrays still carry their element type's alignment. Requiring a
      defined element size also rules out arrays of unsized types. *)
  Lemma tblockR_array_zero t q sz :
    size_of σ t = Some sz ->
    tblockR (Tarray t 0) q -|- validR ** aligned_ofR t.
  Proof.
    move=> Hsz.
    rewrite /tblockR /= Hsz /= align_of_array aligned_ofR.unlock.
    case: (align_of_size_of' _ _ Hsz) => al [Hal _].
    rewrite Hal blockR_eq /blockR_def /= _offsetR_sub_0 ?right_id //.
    iSplit.
    - iIntros "[$ A]". iExists al. by iFrame.
    - iIntros "[$ A]". iDestruct "A" as (a) "[%Ha A]".
      by simplify_eq.
  Qed.

  (** Splitting retains both byte ownership and validity of the split point. *)
  Lemma blockR_add (n m : N) (q : cQp.t) :
    blockR (n + m) q -|- blockR n q ** .[ Tbyte ! Z.of_N n ] |-> blockR m q.
  Proof.
    rewrite blockR_eq /blockR_def N2Nat.inj_add seq_app big_sepL_app.
    rewrite _offsetR_sep _offsetR_big_sepL _offsetR_sub_sub N2Z.inj_add.
    rewrite Nat.add_0_l -(fmap_add_seq_0 (N.to_nat n)) big_sepL_fmap.
    setoid_rewrite _offsetR_sub_sub. setoid_rewrite Nat2Z.inj_add.
    have Hn : Z.of_nat (N.to_nat n) = Z.of_N n by lia.
    rewrite Hn. iSplit.
    - iIntros "(#E & L & R)".
      destruct (N.to_nat m) as [|k] eqn:Hm.
      + have -> : m = 0%N by lia. rewrite Z.add_0_r. iFrame "E L R".
      + iDestruct "R" as "[R0 R]".
        iEval (rewrite Z.add_0_r) in "R0".
        iDestruct (observe (.[ Tbyte ! Z.of_N n ] |-> validR) with "R0") as "#B".
        simpl. rewrite Z.add_0_r. iFrame "E L R0 R B".
    - iIntros "([_ L] & E & R)". iFrame.
  Qed.

  #[local] Instance blockR_valid_end (n : N) (q : cQp.t) :
    Observe (.[ Tbyte ! Z.of_N n ] |-> validR) (blockR n q).
  Proof. rewrite blockR_eq /blockR_def. apply _. Qed.

  (** Chunks may have size zero; the final validity fact remains necessary. *)
  Lemma blockR_chunks (n : nat) (sz : N) (q : cQp.t) :
    blockR (N.of_nat n * sz) q -|-
    .[ Tbyte ! Z.of_N (N.of_nat n * sz) ] |-> validR **
    [∗ list] i ∈ seq 0 n, .[ Tbyte ! Z.of_N (N.of_nat i * sz) ] |-> blockR sz q.
  Proof.
    induction n as [|n IH].
    - rewrite /= blockR_eq /blockR_def /=. done.
    - have Hsz : (N.of_nat (S n) * sz = N.of_nat n * sz + sz)%N by lia.
      rewrite Hsz blockR_add IH seq_S big_sepL_app /= right_id.
      iSplit.
      + iIntros "([_ L] & R)".
        iDestruct (observe (.[ Tbyte ! Z.of_N (N.of_nat n * sz) ] |->
          .[ Tbyte ! Z.of_N sz ] |-> validR) with "R") as "#E".
        iEval (rewrite _offsetR_sub_sub -N2Z.inj_add) in "E".
        iFrame "L R E".
      + iIntros "(_ & L & R)".
        iDestruct (observe (.[ Tbyte ! Z.of_N (N.of_nat n * sz) ] |-> validR) with "R") as "#E".
        iFrame "L R E".
  Qed.

  (** Whole element sizes preserve alignment between valid byte-offset pointers. *)
  Lemma aligned_ofR_byte_sub (t : Rtype) (sz i : N) :
    size_of σ t = Some sz ->
    aligned_ofR t ** validR ** .[ Tbyte ! Z.of_N (i * sz) ] |-> validR
    |-- .[ Tbyte ! Z.of_N (i * sz) ] |-> aligned_ofR t.
  Proof.
    intros Hsz. apply Rep_entails_at => p.
    rewrite !_at_sep !_at_offsetR !_at_validR !aligned_ofR_aligned_ptr_ty.
    destruct (align_of_size_of' _ _ Hsz) as (al & Hal & Hal0 & Hdvd).
    iIntros "(%Hp & V & _)".
    destruct (ptr_vaddr (p .[ Tbyte ! Z.of_N (i * sz) ])) as [va'|] eqn:Hva'.
    2: { iPureIntro. exists al. split; first done. by right. }
    have Heval : eval_offset σ (o_sub σ Tbyte (Z.of_N (i * sz))) = Some (Z.of_N (i * sz)).
    { by rewrite (eval_o_sub' (σ:=σ) (ty:=Tbyte) 1 eq_refl) Z.mul_1_l. }
    iDestruct (offset_inv_pinned_ptr_pure _ _ va' p Heval Hva' with "V") as %[Hge Hpva].
    iPureIntro. exists al. split; first done. left. exists va'. split; first done.
    move: Hp => [al2 [Hal2 Hpal]].
    have Halq : al2 = al by congruence. rewrite Halq in Hpal.
    destruct Hpal as [[va [Hva Hdva]]|Hnone]; last by rewrite Hnone in Hpva.
    rewrite Hpva in Hva. injection Hva as Hva. rewrite -Hva in Hdva.
    have Hz : (Z.of_N al | Z.of_N va')%Z.
    { have -> : (Z.of_N va' =
          Z.of_N (Z.to_N (Z.of_N va' - Z.of_N (i * sz))) + Z.of_N (i * sz))%Z
        by rewrite Z2N.id//; lia.
      apply Z.divide_add_r.
      - exact: N2Z_inj_divide.
      - apply N2Z_inj_divide. by apply N.divide_mul_r. }
    have Hpos : (0 < Z.of_N al)%Z by lia.
    have Hnn : (0 <= Z.of_N va')%Z by lia.
    move: (Z2N_inj_divide _ _ Hpos Hnn Hz). by rewrite !N2Z.id.
  Qed.

  (** Decompose an array into individual components. One past the end is
      valid but stores nothing. Keep the base alignment even when there are
      no elements to supply it. *)
  Lemma tblockR_array_better t n q sz :
        size_of σ t = Some sz ->
        tblockR (Tarray t n) q
    -|- aligned_ofR t **
        .[ Tbyte ! Z.of_N (n * sz) ] |-> validR **
        [∗list] i ∈ seq 0 (N.to_nat n),
           .[ Tbyte ! Z.of_N (N.of_nat i * sz) ] |-> tblockR t q.
  Proof.
    intros Hsz.
    destruct (align_of_size_of' _ _ Hsz) as (al & Hal & Hal0 & Hdvd).
    have HA : aligned_ofR t -|- alignedR al.
    { rewrite aligned_ofR.unlock Hal. iSplit.
      - iIntros "(%a & %Ha & H)". by simplify_eq.
      - iIntros "H". iExists al. by iFrame. }
    rewrite /tblockR /= Hsz /= align_of_array Hal.
    have HC := blockR_chunks (N.to_nat n) sz q. rewrite N2Nat.id in HC.
    setoid_rewrite <- HA.
    iSplit.
    - iIntros "(B & #A)".
      iDestruct (observe validR with "B") as "#Vp".
      iEval (rewrite HC) in "B". iDestruct "B" as "[E B]". iFrame "A E".
      iApply (big_sepL_impl with "B"). iIntros "!>" (k i Hi) "B".
      rewrite _offsetR_sep.
      iDestruct (observe (.[ Tbyte ! Z.of_N (N.of_nat i * sz) ] |-> validR) with "B") as "#V".
      iFrame "B". iApply (aligned_ofR_byte_sub t sz (N.of_nat i) Hsz). by iFrame "A Vp V".
    - rewrite HC. iIntros "(#A & E & B)". iFrame "A E".
      iApply (big_sepL_impl with "B"). iIntros "!>" (k i Hi) "B".
      rewrite _offsetR_sep. iDestruct "B" as "[$ _]".
  Qed.

End with_Σ.
