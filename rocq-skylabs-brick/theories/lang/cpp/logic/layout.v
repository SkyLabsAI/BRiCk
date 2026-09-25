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
    (* TODO: prove the general byte-block splitting and alignment transport.
       The empty case is proved independently by [tblockR_array_zero]. *)
  Admitted.

  (* TODO: migrate clients to the statement above, and drop this. *)
  Lemma tblockR_array : forall t n q,
        is_Some (size_of σ t) ->
        tblockR (Tarray t n) q
    -|- aligned_ofR t **
        _sub t (Z.of_N n) |-> validR **
        [∗list] i ↦ _ ∈ repeat () (BinNatDef.N.to_nat n),
           _sub t (Z.of_nat i) |-> tblockR t q.
  Proof. Admitted.

End with_Σ.
