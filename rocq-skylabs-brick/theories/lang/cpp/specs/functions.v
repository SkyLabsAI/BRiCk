(*
 * Copyright (c) 2020-21 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.iris.extra.bi.ChargeCompat.
Require Import bluerock.iris.extra.bi.telescopes.
Require Import bluerock.lang.cpp.logic.entailsN.
Require Import bluerock.iris.extra.bi.errors.
Require Import bluerock.iris.extra.proofmode.proofmode.	(** Early to get the right [ident] *)
Require Import bluerock.lang.cpp.logic.
Require Import bluerock.lang.cpp.specs.cpp_specs.

#[local] Set Printing Universes.
#[local] Set Printing Coercions.

(** * Wrappers to build [function_spec] from a [WithPrePost] *)

Notation WithPrePostO PROP := (WpSpecO PROP ptr ptr).

#[local] Notation SPEC := (WpSpec_cpp_ptr) (only parsing).

(* A specification for a function *)
Definition SFunction `{Σ : cpp_logic} {cc : calling_conv} {ar : function_arity}
    (ret : type) (targs : list type) (PQ : SPEC)
    : function_spec :=
  {| fs_cc        := cc
   ; fs_arity     := ar
   ; fs_return    := ret
   ; fs_arguments := targs
   ; fs_spec      := wp_specD PQ |}.

(* A specification for a constructor *)
Definition SConstructor `{Σ : cpp_logic, resolve : genv} {cc : calling_conv} {ar : function_arity}
    (class : globname) (targs : list type) (PQ : ptr -> SPEC)
    : function_spec :=
  let this_type := Tmut (Tnamed class) in
  SFunction (cc:=cc) (Tmut Tvoid) (Tconst (Tptr this_type) :: targs) (ar:=ar)
            (\arg{this : ptr} "this" this
             \pre this |-> tblockR (Tnamed class) 1$m
             \exact PQ this).

(* A specification for a destructor *)
Definition SDestructor `{Σ : cpp_logic, resolve : genv} {cc : calling_conv}
    (class : globname) (PQ : ptr -> SPEC)
    : function_spec :=
  let this_type := Tmut (Tnamed class) in
  (** ^ NOTE the size of an object might be different in the presence
      of virtual base classes. *)
  SFunction (cc:=cc) (Tmut Tvoid) (Tconst (Tptr this_type) :: nil)
           (\arg{this} "this" this
            \exact add_post (_at this (tblockR (Tnamed class) 1$m)) (PQ this)).

(* A specification for a method *)
(** Sometimes, especially after a virtual function resolution,
 *  [this] pointer needs to be adjusted before a call. *)
#[local] Definition SMethodOptCast_wpp`{Σ : cpp_logic}
    (base_to_derived : option offset) (wpp : ptr -> SPEC)
  : SPEC :=
  \arg{this : ptr} "this"
   (if base_to_derived is Some o then (this ,, o ) else this)
  \exact (wpp this).
#[local] Definition SMethodOptCast `{Σ : cpp_logic} {cc : calling_conv} {ar : function_arity}
    (class : globname) (base_to_derived : option offset) (qual : type_qualifiers)
    (ret : type) (targs : list type) (PQ : ptr -> SPEC) : function_spec :=
  let class_type := Tnamed class in
  let this_type := Tqualified qual class_type in
  SFunction (cc:=cc) ret (Tconst (Tptr this_type) :: targs) (ar:=ar)
    (SMethodOptCast_wpp base_to_derived PQ).
Definition SMethodCast `{Σ : cpp_logic} {cc : calling_conv} {ar : function_arity}
    (class : globname) (base_to_derived : offset) (qual : type_qualifiers)
    (ret : type) (targs : list type) (PQ : ptr -> SPEC) : function_spec :=
  SMethodOptCast (cc:=cc) class (Some base_to_derived) qual ret targs (ar:=ar) PQ.
Definition SMethod `{Σ : cpp_logic} {cc : calling_conv} {ar : function_arity}
    (class : globname) (qual : type_qualifiers) (ret : type) (targs : list type)
    (PQ : ptr -> SPEC) : function_spec :=
  SMethodOptCast (cc:=cc) class None qual ret targs (ar:=ar) PQ.

Section with_cpp.
  Context `{Σ : cpp_logic} {resolve:genv}.

  #[local] Notation _base := (o_base resolve).
  #[local] Notation _derived := (o_derived resolve).

  (** The following monotonicity lemmas are (i) stated so that they
      don't force a pair of related SPECs to share universes and (ii)
      proved so that they don't constrain the universes [Y1], [Y2]
      from above. The TC instances are strictly less useful, as they
      necessarily give up on both (i) and (ii). *)
  Section SFunction.
    Import disable_proofmode_telescopes.
    Context {cc : calling_conv} {ar : function_arity}.
    Context (ret : type) (targs : list type).

    Lemma SFunction_mono wpp1 wpp2 :
      wpspec_entails wpp1 wpp2 ->
      fs_entails
        (SFunction (cc:=cc) (ar:=ar) ret targs wpp1)
        (SFunction (cc:=cc) (ar:=ar) ret targs wpp2).
    Proof.
      intros Hwpp. iSplit; first by rewrite/type_of_spec. simpl.
      iIntros "!>" (vs K) "wpp". by iApply Hwpp.
    Qed.

    Lemma SFunction_mono_fupd wpp1 wpp2 :
      wpspec_entails_fupd wpp1 wpp2 ->
      fs_entails_fupd
        (SFunction (cc:=cc) (ar:=ar) ret targs wpp1)
        (SFunction (cc:=cc) (ar:=ar) ret targs wpp2).
    Proof.
      (* (FM-2648) TODO duplicated from [SFunction_mono] *)
      intros Hwpp. iSplit; first by rewrite/type_of_spec. simpl.
      iIntros "!>" (vs K) "wpp". by iApply Hwpp.
    Qed.

    #[global] Instance: Params (@SFunction) 6 := {}.
    #[global] Instance SFunction_ne : NonExpansive (SFunction (cc:=cc) ret targs).
    Proof.
      intros n wpp1 wpp2 Hwpp. split; by rewrite/type_of_spec/=.
    Qed.

    #[global] Instance SFunction_proper :
      Proper (equiv ==> equiv) (SFunction (cc:=cc) ret targs).
    Proof. exact: ne_proper. Qed.

    #[global] Instance SFunction_mono' :
      Proper (wpspec_entails ==> fs_entails) (SFunction (cc:=cc) ret targs).
    Proof. repeat intro. by apply SFunction_mono. Qed.

    #[global] Instance SFunction_flip_mono' :
      Proper (flip wpspec_entails ==> flip fs_entails)
        (SFunction (cc:=cc) ret targs).
    Proof. solve_proper. Qed.

    #[global] Instance SFunction_mono_fupd' :
      Proper (wpspec_entails_fupd ==> fs_entails_fupd)
        (SFunction (cc:=cc) ret targs).
    Proof. repeat intro. by apply SFunction_mono_fupd. Qed.

    #[global] Instance SFunction_flip_mono_fupd' :
      Proper (flip wpspec_entails_fupd ==> flip fs_entails_fupd)
        (SFunction (cc:=cc) ret targs).
    Proof. solve_proper. Qed.
  End SFunction.

  Section SConstructor.
    Import disable_proofmode_telescopes.
    Context {cc : calling_conv} {ar : function_arity}.
    Context (class : globname) (targs : list type).
    Implicit Types (wpp : ptr → WpSpec mpredI ptr ptr).

    Lemma SConstructor_mono wpp1 wpp2 :
      (forall this, wpspec_entails (wpp1 this) (wpp2 this)) ->
      fs_entails
        (SConstructor (cc:=cc) class targs (ar:=ar) wpp1)
        (SConstructor (cc:=cc) class targs (ar:=ar) wpp2).
    Proof.
      rewrite /wpspec_entails/wp_specD/=.
      intros Hwpp; apply SFunction_mono => /=.
      iIntros (vs K) "[%this wpp] /="; iExists this.
      rewrite /exact_spec 2!pre_ok -/([]++[this]) 2!arg_ok.
      iDestruct "wpp" as "[$ (% & % & wpp)]".
      iExists _; iFrame; iSplit; [done|].
      by iApply Hwpp.
    Qed.
    #[global] Instance: Params (@SConstructor) 7 := {}.

    Lemma SConstructor_mono_fupd wpp1 wpp2 :
      (forall this, wpspec_entails_fupd (wpp1 this) (wpp2 this)) ->
      fs_entails_fupd
        (SConstructor (cc:=cc) class targs (ar:=ar) wpp1)
        (SConstructor (cc:=cc) class targs (ar:=ar) wpp2).
    Proof.
      (* (FM-2648) TODO duplicated from [SConstructor_mono] *)
      rewrite /wpspec_entails_fupd/wp_specD/=.
      intros Hwpp; apply SFunction_mono_fupd => /=.
      iIntros (vs K) "[%this wpp] /="; iExists this.
      rewrite /exact_spec 2!pre_ok -/([]++[this]) 2!arg_ok.
      iDestruct "wpp" as "[$ (% & % & wpp)]".
      iExists _; iFrame; iSplitR; [done|].
      by iApply Hwpp.
    Qed.

    #[global] Instance SConstructor_mono' :
      Proper (pointwise_relation _ wpspec_entails ==> fs_entails)
        (SConstructor (cc:=cc) class targs (ar:=ar)).
    Proof. repeat intro. by apply SConstructor_mono. Qed.

    #[global] Instance SConstructor_flip_mono' :
      Proper (flip (pointwise_relation _ wpspec_entails) ==> flip fs_entails)
        (SConstructor (cc:=cc) class targs (ar:=ar)).
    Proof. solve_proper. Qed.

    #[global] Instance SConstructor_mono_fupd' :
      Proper (pointwise_relation _ wpspec_entails_fupd ==> fs_entails_fupd)
        (SConstructor (cc:=cc) class targs (ar:=ar)).
    Proof. repeat intro. by apply SConstructor_mono_fupd. Qed.

    #[global] Instance SConstructor_flip_mono_fupd' :
      Proper (flip (pointwise_relation _ wpspec_entails_fupd) ==> flip fs_entails_fupd)
        (SConstructor (cc:=cc) class targs (ar:=ar)).
    Proof. solve_proper. Qed.

    #[global] Instance SConstructor_ne n :
      Proper (pointwise_relation _ (dist n) ==> dist n)
        (SConstructor (cc:=cc) class targs (ar:=ar)).
    Proof. intros ???. apply SFunction_ne. repeat f_equiv. Qed.
    #[global] Instance SConstructor_proper :
      Proper (pointwise_relation _ equiv ==> equiv)
        (SConstructor (cc:=cc) class targs (ar:=ar)).
    Proof. intros ???. apply SFunction_proper. repeat f_equiv. Qed.
  End SConstructor.

  Section SDestructor.
    Import disable_proofmode_telescopes.
    Context {cc : calling_conv} (class : globname).
    Implicit Types (wpp : ptr → WpSpec mpredI ptr ptr).

    Lemma SDestructor_mono wpp1 wpp2 :
      (forall this, wpspec_entails (wpp1 this) (wpp2 this)) ->
      fs_entails
        (SDestructor (cc:=cc) class wpp1)
        (SDestructor (cc:=cc) class wpp2).
    Proof.
      rewrite /wpspec_entails/wp_specD/=/SDestructor.
      intros Hwpp; apply SFunction_mono.
      iIntros (vs K) "[%this wpp] /="; iExists this.
      rewrite -/([]++[λ _: ptr, _]) 2!post_ok.
      rewrite -/([]++[this])%list 2!arg_ok.
      iDestruct "wpp" as "(% & % & wpp)".
      iExists _; iFrame; iSplit; [done|].
      by iApply Hwpp.
    Qed.
    #[global] Instance: Params (@SDestructor) 5 := {}.

    Lemma SDestructor_mono_fupd wpp1 wpp2 :
      (forall this, wpspec_entails_fupd (wpp1 this) (wpp2 this)) ->
      fs_entails_fupd
        (SDestructor (cc:=cc) class wpp1)
        (SDestructor (cc:=cc) class wpp2).
    Proof.
      (* (FM-2648) TODO duplicated from [SDestructor_mono] *)
      rewrite /wpspec_entails_fupd/wp_specD/=/SDestructor.
      intros Hwpp; apply SFunction_mono_fupd.
      iIntros (vs K) "[%this wpp] /="; iExists this.
      rewrite -/([]++[λ _: ptr, _]) 2!post_ok.
      rewrite -/([]++[this])%list 2!arg_ok.
      iDestruct "wpp" as "(% & % & wpp)".
      iExists _; iFrame; iSplitR; [done|].
      iMod (Hwpp with "wpp") as "H". iIntros "!>".
      iApply (spec_internal_frame with "[] H").
      iIntros (r) "H tb".
      iMod "H". by iApply ("H" with "tb").
    Qed.

    #[global] Instance SDestructor_mono' :
      Proper (pointwise_relation _ wpspec_entails ==> fs_entails)
        (SDestructor (cc:=cc) class).
    Proof. repeat intro. by apply SDestructor_mono. Qed.

    #[global] Instance SDestructor_flip_mono' :
      Proper (flip(pointwise_relation _ wpspec_entails) ==> flip fs_entails)
        (SDestructor (cc:=cc) class).
    Proof. solve_proper. Qed.

    #[global] Instance SDestructor_mono_fupd' :
      Proper (pointwise_relation _ wpspec_entails_fupd ==> fs_entails_fupd)
        (SDestructor (cc:=cc) class).
    Proof. repeat intro. by apply SDestructor_mono_fupd. Qed.

    #[global] Instance SDestructor_flip_mono_fupd' :
      Proper (flip (pointwise_relation _ wpspec_entails_fupd) ==> flip fs_entails_fupd)
        (SDestructor (cc:=cc) class).
    Proof. solve_proper. Qed.

    #[global] Instance SDestructor_ne n :
      Proper (pointwise_relation _ (dist n) ==> dist n)
        (SDestructor (cc:=cc) class).
    Proof. intros ???. apply SFunction_ne. repeat f_equiv. Qed.
    #[global] Instance SDestructor_proper :
      Proper (pointwise_relation _ equiv ==> equiv)
        (SDestructor (cc:=cc) class).
    Proof. intros ???. apply SFunction_proper. repeat f_equiv. Qed.
  End SDestructor.

  Section SMethod.
    Import disable_proofmode_telescopes.
    Context {cc : calling_conv} {ar : function_arity}.
    Context (class : globname) (qual : type_qualifiers).
    Context (ret : type) (targs : list type).

    (** We could derive [SMethod_mono] from the following
        [SMethod_wpspec_monoN]. We retain this proof because it's easier
        to understand and it goes through without [BiEntailsN]. *)
    #[local] Lemma SMethodOptCast_mono cast wpp1 wpp2 :
      (∀ this, wpspec_entails (wpp1 this) (wpp2 this)) ->
      fs_entails
        (SMethodOptCast (cc:=cc) class cast qual ret targs (ar:=ar) wpp1)
        (SMethodOptCast (cc:=cc) class cast qual ret targs (ar:=ar) wpp2).
    Proof.
      intros Hwpp.
      apply SFunction_mono => vs K.
      rewrite /= /exact_spec.
      f_equiv => this.
      rewrite -(app_nil_l [_]) !arg_ok.
      repeat f_equiv. apply Hwpp.
    Qed.

    #[local] Lemma SMethodOptCast_None_Some_mono (off2 : offset) wpp1 wpp2 :
      (* NOTE (JH): contravariant use of casts *)
      (forall (thisp : ptr), wpspec_entails (wpp1 (thisp ,, off2)) (wpp2 thisp)) ->
      fs_entails
        (SMethodOptCast class None qual ret targs wpp1)
        (SMethodOptCast class (Some off2) qual ret targs wpp2).
    Proof.
      intros Hwpp.
      apply SFunction_mono => argps K.
      rewrite /exact_spec !add_with_equiv.
      iIntros "H"; iDestruct "H" as (thisp) "wpp";
        iExists (thisp ,, off2).
      rewrite !add_arg_equiv.
      destruct argps; first by done.
      iDestruct "wpp" as "[$ wpp]".
      by iApply Hwpp.
    Qed.

    #[local] Lemma SMethodOptCast_mono_fupd cast wpp1 wpp2 :
      (∀ this, wpspec_entails_fupd (wpp1 this) (wpp2 this)) ->
      fs_entails_fupd
        (SMethodOptCast (cc:=cc) class cast qual ret targs (ar:=ar) wpp1)
        (SMethodOptCast (cc:=cc) class cast qual ret targs (ar:=ar) wpp2).
    Proof.
      (* (FM-2648) TODO duplicated from [SMethodOptCast_mono] *)
      intros Hwpp.
      apply SFunction_mono_fupd => vs K.
      rewrite /= /exact_spec.
      iDestruct 1 as (this) "wpp". iExists this.
      move: Hwpp.
      rewrite -(app_nil_l [_]) !arg_ok.
      intros.
      iDestruct "wpp" as "(% & % & wpp)".
      iExists _; iFrame; iSplitR; [done|].
      by iApply Hwpp.
    Qed.

    Lemma SMethodCast_mono cast wpp1 wpp2 :
      (∀ this, wpspec_entails (wpp1 this) (wpp2 this)) ->
      fs_entails
        (SMethodOptCast (cc:=cc) class cast qual ret targs (ar:=ar) wpp1)
        (SMethodOptCast (cc:=cc) class cast qual ret targs (ar:=ar) wpp2).
    Proof. exact: SMethodOptCast_mono. Qed.

    Lemma SMethodCast_None_Some_mono (off2 : offset) wpp1 wpp2 :
      (* NOTE (JH): contravariant use of casts *)
      (forall (thisp : ptr), wpspec_entails (wpp1 (thisp ,, off2)) (wpp2 thisp)) ->
      fs_entails
        (SMethodOptCast class None qual ret targs wpp1)
        (SMethodOptCast class (Some off2) qual ret targs wpp2).
    Proof. exact: SMethodOptCast_None_Some_mono. Qed.

    Lemma SMethod_mono wpp1 wpp2 :
      (∀ this, wpspec_entails (wpp1 this) (wpp2 this)) ->
      fs_entails
        (SMethod (cc:=cc) class qual ret targs (ar:=ar) wpp1)
        (SMethod (cc:=cc) class qual ret targs (ar:=ar) wpp2).
    Proof. exact: SMethodOptCast_mono. Qed.

    Lemma SMethodCast_mono_fupd cast wpp1 wpp2 :
      (∀ this, wpspec_entails_fupd (wpp1 this) (wpp2 this)) ->
      fs_entails_fupd
        (SMethodOptCast (cc:=cc) class cast qual ret targs (ar:=ar) wpp1)
        (SMethodOptCast (cc:=cc) class cast qual ret targs (ar:=ar) wpp2).
    Proof. exact: SMethodOptCast_mono_fupd. Qed.

    Lemma SMethod_mono_fupd wpp1 wpp2 :
      (∀ this, wpspec_entails_fupd (wpp1 this) (wpp2 this)) ->
      fs_entails_fupd
        (SMethod (cc:=cc) class qual ret targs (ar:=ar) wpp1)
        (SMethod (cc:=cc) class qual ret targs (ar:=ar) wpp2).
    Proof. exact: SMethodOptCast_mono_fupd. Qed.

    #[local] Lemma SMethodOptCast_wpspec_monoN
        c wpp1 wpp2 vs K n :
      (∀ this, wpspec_entailsN n (wpp1 this) (wpp2 this)) ->
      SMethodOptCast_wpp c wpp2 vs K ⊢{n}
      SMethodOptCast_wpp c wpp1 vs K.
    Proof.
      move=>Hwpp /=. rewrite /exact_spec. f_equiv=>this.
      rewrite -(app_nil_l [_]) !arg_ok.
      repeat f_equiv. apply Hwpp.
    Qed.

    #[local] Lemma SMethodOptCast_ne cast wpp1 wpp2 n :
      (∀ this, wpspec_dist n (wpp1 this) (wpp2 this)) ->
      SMethodOptCast (cc:=cc) class cast qual ret targs (ar:=ar) wpp1 ≡{n}≡
      SMethodOptCast (cc:=cc) class cast qual ret targs (ar:=ar) wpp2.
    Proof.
      setoid_rewrite wpspec_dist_entailsN=>Hwpp.
      rewrite/SMethodOptCast. f_equiv=>vs K /=. apply dist_entailsN.
      split; apply SMethodOptCast_wpspec_monoN=>this; by destruct (Hwpp this).
    Qed.

    Lemma SMethodCast_ne cast wpp1 wpp2 n :
      (∀ this, wpspec_dist n (wpp1 this) (wpp2 this)) ->
      SMethodCast (cc:=cc) class cast qual ret targs (ar:=ar) wpp1 ≡{n}≡
      SMethodCast (cc:=cc) class cast qual ret targs (ar:=ar) wpp2.
    Proof. exact: SMethodOptCast_ne. Qed.

    Lemma SMethod_ne wpp1 wpp2 n :
      (∀ this, wpspec_dist n (wpp1 this) (wpp2 this)) ->
      SMethod (cc:=cc) class qual ret targs (ar:=ar) wpp1 ≡{n}≡
      SMethod (cc:=cc) class qual ret targs (ar:=ar) wpp2.
    Proof. exact: SMethodOptCast_ne. Qed.

    #[local] Lemma SMethodOptCast_proper cast wpp1 wpp2 :
      (∀ this, wpspec_equiv (wpp1 this) (wpp2 this)) ->
      SMethodOptCast (cc:=cc) class cast qual ret targs (ar:=ar) wpp1 ≡
      SMethodOptCast (cc:=cc) class cast qual ret targs (ar:=ar) wpp2.
    Proof.
      setoid_rewrite wpspec_equiv_spec=>Hwpp. apply function_spec_equiv_split.
      split; apply SMethodCast_mono=>this; by destruct (Hwpp this).
    Qed.
    Lemma SMethodCast_proper cast wpp1 wpp2 :
      (∀ this, wpspec_equiv (wpp1 this) (wpp2 this)) ->
      SMethodCast (cc:=cc) class cast qual ret targs (ar:=ar) wpp1 ≡
      SMethodCast (cc:=cc) class cast qual ret targs (ar:=ar) wpp2.
    Proof. exact: SMethodOptCast_proper. Qed.
    Lemma SMethod_proper wpp1 wpp2 :
      (∀ this, wpspec_equiv (wpp1 this) (wpp2 this)) ->
      SMethod (cc:=cc) class qual ret targs (ar:=ar) wpp1 ≡
      SMethod (cc:=cc) class qual ret targs (ar:=ar) wpp2.
    Proof. exact: SMethodOptCast_proper. Qed.

    #[global] Instance: Params (@SMethodCast) 9 := {}.
    #[global] Instance: Params (@SMethod) 8 := {}.
    #[global] Instance SMethodCast_ne' cast n :
      Proper (dist (A:=ptr -d> WithPrePostO mpredI) n ==> dist n)
        (SMethodCast (cc:=cc) class cast qual ret targs (ar:=ar)).
    Proof. repeat intro. by apply SMethodCast_ne. Qed.
    #[global] Instance SMethod_ne' n :
      Proper (dist (A:=ptr -d> WithPrePostO mpredI) n ==> dist n)
        (SMethod (cc:=cc) class qual ret targs (ar:=ar)).
    Proof. repeat intro. by apply SMethod_ne. Qed.

    #[global] Instance SMethodCast_proper' cast :
      Proper (equiv (A:=ptr -d> WithPrePostO mpredI) ==> equiv)
        (SMethodCast (cc:=cc) class cast qual ret targs (ar:=ar)).
    Proof. exact: ne_proper. Qed.
    #[global] Instance SMethod_proper' :
      Proper (equiv (A:=ptr -d> WithPrePostO mpredI) ==> equiv)
        (SMethod (cc:=cc) class qual ret targs (ar:=ar)).
    Proof. exact: ne_proper. Qed.

    #[global] Instance SMethodCast_mono' cast :
      Proper (pointwise_relation _ wpspec_entails ==> fs_entails)
        (SMethodCast (cc:=cc) class cast qual ret targs (ar:=ar)).
    Proof. repeat intro. by apply SMethodCast_mono. Qed.
    #[global] Instance SMethod_mono' :
      Proper (pointwise_relation _ wpspec_entails ==> fs_entails)
        (SMethod (cc:=cc) class qual ret targs (ar:=ar)).
    Proof. repeat intro. by apply SMethod_mono. Qed.

    #[global] Instance SMethodCast_flip_mono' cast :
      Proper (flip (pointwise_relation _ wpspec_entails) ==> flip fs_entails)
        (SMethodCast (cc:=cc) class cast qual ret targs (ar:=ar)).
    Proof. repeat intro. by apply SMethodCast_mono. Qed.
    #[global] Instance SMethod_flip_mono' :
      Proper (flip (pointwise_relation _ wpspec_entails) ==> flip fs_entails)
        (SMethod (cc:=cc) class qual ret targs (ar:=ar)).
    Proof. repeat intro. by apply SMethod_mono. Qed.

    #[global] Instance SMethodCast_mono_fupd' cast :
      Proper (pointwise_relation _ wpspec_entails_fupd ==> fs_entails_fupd)
        (SMethodCast (cc:=cc) class cast qual ret targs (ar:=ar)).
    Proof. repeat intro. by apply SMethodCast_mono_fupd. Qed.
    #[global] Instance SMethod_mono_fupd' :
      Proper (pointwise_relation _ wpspec_entails_fupd ==> fs_entails_fupd)
        (SMethod (cc:=cc) class qual ret targs (ar:=ar)).
    Proof. repeat intro. by apply SMethod_mono_fupd. Qed.

    #[global] Instance SMethodCast_flip_mono_fupd' cast :
      Proper (flip (pointwise_relation _ wpspec_entails_fupd) ==> flip fs_entails_fupd)
        (SMethodCast (cc:=cc) class cast qual ret targs (ar:=ar)).
    Proof. repeat intro. by apply SMethodCast_mono_fupd. Qed.
    #[global] Instance SMethod_flip_mono_fupd' :
      Proper (flip (pointwise_relation _ wpspec_entails_fupd) ==> flip fs_entails_fupd)
        (SMethod (cc:=cc) class qual ret targs (ar:=ar)).
    Proof. repeat intro. by apply SMethod_mono_fupd. Qed.
  End SMethod.

End with_cpp.
