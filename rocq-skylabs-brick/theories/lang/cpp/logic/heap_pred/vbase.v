(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** * Representation predicates for classes with virtual bases

A class [C] with virtual bases (see [VStruct]) has two layouts, so it has
two kinds of [Rep]:

- a _pre-[Rep]_ for its non-virtual part: its fields and its direct
  non-virtual bases, at static offsets ([_field], [_base]). This is all
  that a base-class subobject of type [C] owns.

- a _full [Rep]_: the pre-[Rep] plus, once for each virtual base [V], the
  [Rep] of [V] at the location of that virtual base, i.e.
  [vbaseR C V R].

For example, with
<<
struct VB { int v; };
struct L : virtual VB { int l; };
struct R : virtual VB { int r; };
struct G : L, R { int g; };
>>
one writes
[[
VBR q v := _field "VB::v" |-> intR q v.
L_pre q l := _field "L::l" |-> intR q l.
LR q l v  := L_pre q l ** vbaseR "L" "VB" (VBR q v).
G_pre q l r g :=
  _base "G" "L" |-> L_pre q l ** _base "G" "R" |-> R_pre q r **
  _field "G::g" |-> intR q g.
GR q l r g v := G_pre q l r g ** vbaseR "G" "VB" (VBR q v).
]]
The one <<VB>> is owned once, by whichever class is the most derived.
*)

Require Import skylabs.lang.cpp.logic.heap_pred.prelude.
Require Import skylabs.lang.cpp.logic.heap_pred.valid.
Require Import skylabs.lang.cpp.logic.heap_pred.simple.
Require Import skylabs.lang.cpp.logic.heap_pred.block.

#[local] Set Printing Coercions.
Implicit Types (σ : genv) (p : ptr) (o : offset).

(** ** Storage of the non-virtual part *)

(** [nv_tblockR cls q] is [q] ownership of the storage of the non-virtual
    part of a class [cls] with virtual bases: what a constructor of [cls]
    consumes and its destructor returns (see [wp_ctor] and [wp_dtor]).
    Compare [tblockR (Tnamed cls) q].

    Like [tblockR] at class types, [nv_tblockR] is abstract: nothing turns
    it into bytes, so the logic never needs the size of the non-virtual
    part. Its intended model is the data of the non-virtual part (see
    [vstruct_layout_ok]) together with a token for [cls] at that address;
    [blockR] of the non-virtual size, suitably aligned, also satisfies the
    axioms below. *)
Parameter nv_tblockR : forall `{Σ : cpp_logic} {σ : genv} (cls : globname) (q : cQp.t), Rep.

(** [vptrR cls q] is [q] ownership of the vtable pointer of the [cls]
    (sub)object it is applied to, once that pointer is installed: a
    constructor of [cls] gets it after initializing the non-virtual bases
    (see [wp_vstruct_initializer_list]) and its destructor gives it back
    (see [wp_dtor]). It belongs in the [Rep] of the non-virtual part,
    next to the fields.

    A conversion to a virtual base reads this pointer to find the virtual
    base (see [wp_lval_cast_derived2vbase]), so it needs a fraction of
    [vptrR]. [vbase_ptr] says where the virtual base is, but it is
    persistent: it holds before the pointer is installed and after the
    object is destroyed. *)
Parameter vptrR : forall `{Σ : cpp_logic} {σ : genv} (cls : globname) (q : cQp.t), Rep.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  Axiom vptrR_timeless : forall cls q, Timeless (vptrR cls q).
  Axiom vptrR_cfractional : forall cls, CFractional (vptrR cls).
  #[global] Existing Instances vptrR_timeless vptrR_cfractional.

  #[global] Instance vptrR_as_cfractional cls : AsCFractional0 (vptrR cls).
  Proof. solve_as_cfrac. Qed.

  Axiom nv_tblockR_timeless : forall cls q, Timeless (nv_tblockR cls q).
  Axiom nv_tblockR_cfractional : forall cls, CFractional (nv_tblockR cls).
  #[global] Existing Instances nv_tblockR_timeless nv_tblockR_cfractional.

  #[global] Instance nv_tblockR_as_cfractional cls : AsCFractional0 (nv_tblockR cls).
  Proof. solve_as_cfrac. Qed.

  (** ** Virtual bases *)

  (** [vbaseR cls vbase R] owns [R] at the virtual base [vbase] of the
      object of class [cls] that it is applied to. *)
  Definition vbaseR (cls vbase : globname) (R : Rep) : Rep :=
    as_Rep (fun p => Exists pvb, vbase_ptr cls vbase p pvb ** pvb |-> R).

  Lemma _at_vbaseR p cls vbase R :
    p |-> vbaseR cls vbase R -|- Exists pvb, vbase_ptr cls vbase p pvb ** pvb |-> R.
  Proof. by rewrite /vbaseR _at_as_Rep. Qed.

  #[global] Instance vbaseR_mono cls vbase :
    Proper (bi_entails ==> bi_entails) (vbaseR cls vbase).
  Proof.
    intros R1 R2 HR. apply Rep_entails_at=>p. rewrite !_at_vbaseR.
    f_equiv=>pvb. by rewrite HR.
  Qed.
  #[global] Instance vbaseR_flip_mono cls vbase :
    Proper (flip bi_entails ==> flip bi_entails) (vbaseR cls vbase).
  Proof. intros R1 R2 HR. by apply vbaseR_mono. Qed.
  #[global] Instance vbaseR_proper cls vbase :
    Proper (equiv ==> equiv) (vbaseR cls vbase).
  Proof. intros R1 R2 HR. split'; by apply vbaseR_mono; rewrite HR. Qed.

  #[global] Instance vbaseR_timeless cls vbase R :
    Timeless R -> Timeless (vbaseR cls vbase R).
  Proof. rewrite /vbaseR. apply _. Qed.
  #[global] Instance vbaseR_persistent cls vbase R :
    Persistent R -> Persistent (vbaseR cls vbase R).
  Proof. rewrite /vbaseR. apply _. Qed.
  #[global] Instance vbaseR_affine cls vbase R :
    Affine R -> Affine (vbaseR cls vbase R).
  Proof. rewrite /vbaseR. apply _. Qed.

  (** The location of the virtual base, with what is there. *)
  Lemma vbaseR_intro p pvb cls vbase R :
    vbase_ptr cls vbase p pvb |-- pvb |-> R -* p |-> vbaseR cls vbase R.
  Proof. rewrite _at_vbaseR. iIntros "#? R". iExists pvb. by iFrame "#∗". Qed.

  (** Knowing where the virtual base is, [vbaseR] is just [R] there. *)
  Lemma vbaseR_elim p pvb cls vbase R :
    vbase_ptr cls vbase p pvb |-- p |-> vbaseR cls vbase R -* pvb |-> R.
  Proof.
    rewrite _at_vbaseR. iIntros "#V (%pvb' & #V' & R)".
    iDestruct (observe_2 [| pvb = pvb' |] with "V V'") as %->. iExact "R".
  Qed.

  (** A (sub)object has each virtual base at one location, so [vbaseR]
      distributes over [**]. *)
  Lemma vbaseR_sep cls vbase R1 R2 :
    vbaseR cls vbase (R1 ** R2) -|- vbaseR cls vbase R1 ** vbaseR cls vbase R2.
  Proof.
    apply Rep_equiv_at=>p. rewrite _at_sep !_at_vbaseR. split'.
    - iIntros "(%pvb & #V & R)". rewrite _at_sep. iDestruct "R" as "[R1 R2]".
      iSplitL "R1"; iExists pvb; by iFrame "#∗".
    - iIntros "[(%pvb1 & #V1 & R1) (%pvb2 & #V2 & R2)]".
      iDestruct (observe_2 [| pvb1 = pvb2 |] with "V1 V2") as %->.
      iExists pvb2. rewrite _at_sep. by iFrame "#∗".
  Qed.

  #[global] Instance vbaseR_cfractional cls vbase (R : cQp.t -> Rep) :
    CFractional R -> CFractional (fun q => vbaseR cls vbase (R q)).
  Proof. intros HR q1 q2. by rewrite HR vbaseR_sep. Qed.

  #[global] Instance vbaseR_observe cls vbase (Q R : Rep) :
    Persistent Q -> Observe Q R -> Observe (vbaseR cls vbase Q) (vbaseR cls vbase R).
  Proof.
    intros ? HQR. apply observe_intro; first apply _.
    apply Rep_entails_at=>p. rewrite _at_sep !_at_vbaseR.
    iIntros "(%pvb & #V & R)". iDestruct (observe (pvb |-> Q) with "R") as "#Q".
    iSplitL; iExists pvb; by iFrame "#∗".
  Qed.
End with_cpp.

#[global] Hint Opaque nv_tblockR vptrR vbaseR : typeclass_instances sl_opacity.
