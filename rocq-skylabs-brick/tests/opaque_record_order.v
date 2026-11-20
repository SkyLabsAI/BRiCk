(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.

(** * Why an opaque record is not below a struct in [GlobDecl_le]

    [GlobDecl_le] relates [Gopaque o] only to itself. One could also put it
    below a [Gstruct] with the same size, alignment, destructor, and
    <<operator delete>>, so that a translation unit seeing the record as
    opaque links with one that sees its body.

    [complete_type_respects_sub_table] and [GlobDecl_ler_join] hold today
    only because that order is absent. The counterexamples below do not
    mention [GlobDecl_le]: they are pairs that such an order would relate. *)

Definition opaque (reason : PrimString.string) : Opaque :=
  Build_Opaque 4 4 "C::~C()" true None reason [].

(** A struct with the metadata of [opaque _], and a member whose type is not
    declared. Type tables are not checked for completeness
    ([complete_type_table] is not part of [translation_unit]), so nothing
    rules this struct out. *)
Definition body : Struct :=
  Build_Struct []
    [mkMember (Nid "m") (Tnamed "Missing") false None {| li_offset := 0 |}]
    [] [] "C::~C()" true None POD 4 4.

Definition opaque_table : type_table := {[ "C"%cpp_name := Gopaque (opaque "r") ]}.
Definition body_table : type_table := {[ "C"%cpp_name := Gstruct body ]}.

(** ** [complete_type] would not be monotone *)

Example opaque_complete : complete_type opaque_table "C".
Proof. by econstructor; [vm_compute|constructor]. Qed.

Example body_incomplete : ¬ complete_type body_table "C".
Proof.
  have Hmissing : ¬ complete_type body_table "Missing".
  { intros H; inversion H; subst;
      first [ by match goal with Hl : _ !! _ = Some _ |- _ => vm_compute in Hl end
            | by match goal with Hb : complete_basic_type _ _ |- _ => inversion Hb end ]. }
  intros H; inversion H; subst;
    last by match goal with Hb : complete_basic_type _ _ |- _ => inversion Hb end.
  match goal with
  | Hl : _ !! _ = Some ?d, Hd : complete_decl _ ?d |- _ =>
      vm_compute in Hl; injection Hl as <-; inversion Hd; subst
  end.
  match goal with
  | Hf : forall m, In m _ -> _ |- _ =>
      apply Hmissing,
        (Hf (mkMember (Nid "m") (Tnamed "Missing") false None {| li_offset := 0 |}))
  end.
  by left.
Qed.

(** The metadata that the order would compare agrees, so it would give
    [type_table_le opaque_table body_table]; with the two facts above, that
    contradicts [complete_type_respects_sub_table]. *)
Example metadata_agrees :
  (opaque "r").(o_size) = body.(s_size) /\
  (opaque "r").(o_alignment) = body.(s_alignment) /\
  (opaque "r").(o_dtor) = body.(s_dtor) /\
  (opaque "r").(o_trivially_destructible) = body.(s_trivially_destructible) /\
  (opaque "r").(o_delete) = body.(s_delete).
Proof. done. Qed.

(** ** [GlobDecl_ler_join] would fail *)

(** Two opaque records that differ only in [o_reason] would both be below
    [Gstruct body], but they are not comparable. *)
Example opaque_reasons_incomparable :
  GlobDecl_le (Gopaque (opaque "r1")) (Gopaque (opaque "r2")) = false /\
  GlobDecl_le (Gopaque (opaque "r2")) (Gopaque (opaque "r1")) = false.
Proof. by vm_compute. Qed.
