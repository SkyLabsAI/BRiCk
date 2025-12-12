(*
 * Copyright (c) 2020-2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.prelude.base.
Require Import bluerock.prelude.numbers.
Require Import bluerock.prelude.list.
Require Import bluerock.iris.extra.proofmode.proofmode.

Require Import bluerock.prelude.arith.z_to_bytes.
Require Import bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.logic.pred.
Require Import bluerock.lang.cpp.logic.path_pred.
Require Import bluerock.lang.cpp.logic.heap_pred.
Require Import bluerock.lang.cpp.logic.translation_unit.
Require Import bluerock.lang.cpp.semantics.
Require Import bluerock.lang.cpp.logic.arr.
Require Export bluerock.lang.cpp.logic.raw.

Require Import bluerock.iris.extra.bi.linearity.

Section with_Σ.
  Context `{Σ : cpp_logic} {σ : genv}.

  (** Convert a <<struct>> to its raw representation.
   Justified by the concept of object representation.
   https://eel.is/c++draft/basic.types.general#def:representation,object
   *)
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

  (** implicit destruction of an aggregate *)
  Axiom implicit_destruct_struct
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
      |-- (Reduce (union_defR tblockR cls un q)) -* |={↑pred_ns}=> tblockR (Tnamed cls) q.

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

  (** decompose an array into individual components
      note that one past the end of an array is a valid location, but
      it doesn't store anything.

      TODO this should move
   *)
  (* TODO a type has a size if and only if it has an alignment *)
  Lemma tblockR_array_better t n q sz :
        size_of σ t = Some sz ->
        tblockR (Tarray t n) q
    -|- .[ Tbyte ! Z.of_N (n * sz) ] |-> validR **
        [∗list] i ∈ seq 0 (N.to_nat n),
           .[ Tbyte ! Z.of_N (N.of_nat i * sz) ] |-> tblockR t q.
  Proof.
    rewrite /tblockR /= => Hsz.
    rewrite Hsz /= align_of_array.
    case: (align_of_size_of _ _ Hsz) => [al [Hal HalSz]].
    rewrite Hal.
    (*
    Unclear if unfolding is recommended, but at least it should be sufficient for a hacky proof;
    maybe we should lift lemmas about [blockR] (not sure which).
    *)
    rewrite blockR_eq /blockR_def.
    rewrite -assoc.
    f_equiv.
    (* Maybe useful? *)
    apply Rep_equiv_at => p.
    (* To finish the proof, we need to rearrange [anyR], use [o_sub_sub] & c and
    [anyR_valid_observe], and reason about pointer alignment. For alignment, we
    need to unfold [alignedR], and maybe [aligned_ptr]. *)
  Admitted.

  (* TODO: migrate client to the statement above, and drop this. *)
  Lemma tblockR_array : forall t n q,
        tblockR (Tarray t n) q
    -|- _sub t (Z.of_N n) |-> validR **
        [∗list] i ↦ _ ∈ repeat () (BinNatDef.N.to_nat n),
           _sub t (Z.of_nat i) |-> tblockR t q.
  Proof. Admitted.

End with_Σ.
