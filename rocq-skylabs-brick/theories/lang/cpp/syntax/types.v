(*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.elpi.derive.
Require Import skylabs.prelude.base.
Require Import skylabs.prelude.bool.
Require Import skylabs.prelude.list.
Require Export skylabs.lang.cpp.syntax.core.
Require Export skylabs.lang.cpp.syntax.extras.


Set Primitive Projections.

Section with_lang.

(** ** Qualifier normalization *)
(**
[decompose_type t] strips any top-level qualifiers from [t] and
returns them, paired with the rest of the type.

The underlying functions [qual_norm] and [qual_norm'] are similar
(see, e.g., [qual_norm_decompose_type]).
 *)
Section qual_norm.
  Context {A : Type}.
  Variable f : type_qualifiers -> type -> A.

  Fixpoint qual_norm' (q : type_qualifiers) (t : type) : A :=
    match t with
    | Tqualified q' t => qual_norm' (merge_tq q q') t
    | _ => f q t
    end.
  #[global] Hint Opaque qual_norm' : typeclass_instances.

  Definition qual_norm : type -> A :=
    qual_norm' QM.
  #[global] Hint Opaque qual_norm : typeclass_instances.
End qual_norm.

Lemma qual_norm'_only_type {T} (f : _ -> T) t : forall q1 q2,
    qual_norm' (fun (_ : type_qualifiers) t => f t) q1 t
    = qual_norm' (fun (_ : type_qualifiers) t => f t) q2 t.
Proof. induction t; simpl; auto. Qed.

Lemma qual_norm_map {T U} (f : T -> U) g ty :
  f (qual_norm g ty) = qual_norm (fun cv t => f (g cv t)) ty.
Proof.
  unfold qual_norm.
  generalize QM.
  induction ty; simpl; intros; eauto.
Qed.

Lemma qual_norm'_Tqualified {A} (f : _ -> _ -> A) cv cv' ty :
  qual_norm' f cv (Tqualified cv' ty) = qual_norm' f (merge_tq cv cv') ty.
Proof. done. Qed.

Definition decompose_type : type -> type_qualifiers * type :=
  qual_norm (fun q t => (q, t)).
#[global] Hint Opaque decompose_type : typeclass_instances.
#[global] Arguments decompose_type !_ / : simpl nomatch, assert.

(**
[take_qualifiers], [drop_qualifiers] return and remove leading
qualifiers.
*)
Definition take_qualifiers : type -> type_qualifiers :=
  qual_norm (fun cv _ => cv).

Fixpoint drop_qualifiers (t : type) : type :=
  match t with
  | Tqualified _ t => drop_qualifiers t
  | _ => t
  end.

(** ** Smart constructors *)

(**
Qualify a type, merging nested qualifiers, suppressing [QM]
qualifiers, and (https://www.eel.is/c++draft/dcl.ref#1) discarding any
cv-qualifiers on reference types.
*)
Definition tqualified' (q : type_qualifiers) (t : type) : type :=
  match t with
  | Tref _ | Trv_ref _ => t
  | _ => match q with QM => t | _ => Tqualified q t end
  end.
#[global] Hint Opaque tqualified' : typeclass_instances.
#[global] Arguments tqualified' _ !_ / : simpl nomatch, assert.

Definition tqualified : type_qualifiers -> type -> type :=
  qual_norm' tqualified'.
#[global] Hint Opaque tqualified : typeclass_instances.
#[global] Arguments tqualified _ !_ / : simpl nomatch, assert.

(**
[tref], [trv_ref] implement reference collapsing.

Background:
https://en.cppreference.com/w/cpp/language/reference#Reference_collapsing
https://www.eel.is/c++draft/dcl.ref#6
https://www.eel.is/c++draft/dcl.ref#5
*)
Definition tref := fix tref (acc : type_qualifiers) (t : type) : type :=
  match t with
  | Tref t | Trv_ref t => tref QM t
  | Tqualified q t => tref (merge_tq acc q) t
  | _ => Tref (tqualified acc t)
  end.
#[global] Hint Opaque tref : typeclass_instances.
#[global] Arguments tref _ !_ / : simpl nomatch, assert.

Definition trv_ref := fix trv_ref (acc : type_qualifiers) (t : type) : type :=
  match t with
  | Tref t => tref QM t
  | Trv_ref t => trv_ref QM t
  | Tqualified q t => trv_ref (merge_tq acc q) t
  | _ => Trv_ref (tqualified acc t)
  end.
#[global] Hint Opaque trv_ref : typeclass_instances.
#[global] Arguments trv_ref _ !_ / : simpl nomatch, assert.

(**
An equivalence relation on types that quotients by "identical to C++".
The equations here are dictated by the fact that [type] is too big for
C++.
*)

Inductive type_equiv : Equiv type :=

(**
Qualifier normalization
*)
| Tqualified_id t : Tqualified QM t ≡ t
| Tqualified_merge q q' t : Tqualified q (Tqualified q' t) ≡ Tqualified (merge_tq q q') t
(*
"An array type whose elements are cv-qualified is also considered to
have the same cv-qualifications as its elements. [...] Cv-qualifiers
applied to an array type attach to the underlying element type."
<https://www.eel.is/c++draft/basic.type.qualifier#3>
*)
| Tqualified_array q t n : Tqualified q (Tarray t n) ≡ Tarray (Tqualified q t) n
(*
"A function or reference type is always cv-unqualified."
<https://www.eel.is/c++draft/basic.type.qualifier#1>
*)
| Tqualified_ref q t : Tqualified q (Tref t) ≡ Tref t
| Tqualified_rv_ref q t : Tqualified q (Trv_ref t) ≡ Trv_ref t
| Tqualified_func q ft : Tqualified q (Tfunction ft) ≡ Tfunction ft
(**
"After producing the list of parameter types, any top-level
cv-qualifiers modifying a parameter type are deleted when forming the
function type."
<https://www.eel.is/c++draft/dcl.fct#5>
*)
| Tqualified_func_param cc ar ret q t args args' :
  Tfunction (@FunctionType _ cc ar ret (args ++ Tqualified q t :: args')) ≡ Tfunction (@FunctionType _ cc ar ret (args ++ t :: args'))

(* Equivalence *)
| type_equiv_refl t : t ≡ t
| type_equiv_sym t u : t ≡ u -> u ≡ t
| type_equiv_trans t u v : t ≡ u -> u ≡ v -> t ≡ v

(* Compatibility *)
| Tptr_proper : Proper (equiv ==> equiv) Tptr
| Tref_proper : Proper (equiv ==> equiv) Tref
| Trv_ref_proper : Proper (equiv ==> equiv) Trv_ref
| Tarray_proper : Proper (equiv ==> eq ==> equiv) Tarray
| Tincomplete_array_proper : Proper (equiv ==> equiv) Tincomplete_array
| Tvariable_array_proper : Proper (equiv ==> eq ==> equiv) Tvariable_array
(* | Tfunction_proper cc ar : Proper (equiv ==> equiv ==> equiv) (@Tfunction cc ar) *)
| Tmember_pointer_proper gn : Proper (equiv ==> equiv) (Tmember_pointer gn)
| Tqualified_proper q : Proper (equiv ==> equiv) (Tqualified q)
.
#[global] Existing Instances
  type_equiv
  Tptr_proper
  Tref_proper
  Trv_ref_proper
  Tarray_proper
  Tmember_pointer_proper
  Tqualified_proper
.
#[global] Instance type_equivalence : Equivalence (≡@{type}) :=
  Build_Equivalence _ type_equiv_refl type_equiv_sym type_equiv_trans.

#[global] Instance Tconst_volatile_proper : Proper (equiv ==> equiv) Tconst_volatile.
Proof. solve_proper. Qed.
#[global] Instance Tconst_proper : Proper (equiv ==> equiv) Tconst.
Proof. solve_proper. Qed.
#[global] Instance Tvolatile_proper : Proper (equiv ==> equiv) Tvolatile.
Proof. solve_proper. Qed.
#[global] Instance Tmut_proper : Proper (equiv ==> equiv) Tmut.
Proof. solve_proper. Qed.

Lemma Tmut_equiv t : Tmut t ≡ t.
Proof. by rewrite Tqualified_id. Qed.

(**
It would be nice to make this the default.
*)
#[local] Arguments decompose_type : simpl never.

(**
[is_qualified t] decides if [t] has top-level qualifiers.

Note: [is_qualified] is incompatible with the equivalence on types.
Counterexample: [Tqualified QM (Tref t) ≡ Tref t].
*)
Definition is_qualified (t : type) : bool :=
  if t is Tqualified _ _ then true else false.

Lemma is_qualified_spec t : is_qualified t <-> ∃ q t', t = Tqualified q t'.
Proof. split=>Hq. by destruct t; eauto. by destruct Hq as (?&?&->). Qed.

Lemma is_qualified_qual q t : is_qualified (Tqualified q t).
Proof. done. Qed.

Section qual_norm.
  Context {A : Type}.
  Implicit Types (f : type_qualifiers -> type -> A).

  (** [qual_norm'] *)

  Lemma qual_norm'_unfold f q t :
    qual_norm' f q t =
      if t is Tqualified q' t'
      then qual_norm' f (merge_tq q q') t'
      else f q t.
  Proof. by destruct t. Qed.

  (**
  We use this relation to state induction principles for things
  defined in terms of [qual_norm'] and [qual_norm].

  Example: [elim: (qual_norm_ok _ ty)] in a goal involving [qual_norm
  f ty] tends to be easier to use than [pattern (qual_norm f ty);
  induction using qual_norm_ind] because one need not repeat the
  function [f] in the proof script.
  *)

  Inductive qual_norm_spec f : type_qualifiers -> type -> A -> Prop :=
  | qual_norm_spec_unqual q t : ~~ is_qualified t -> qual_norm_spec f q t (f q t)
  | qual_norm_spec_qual q q' t' ret :
    qual_norm_spec f (merge_tq q q') t' ret ->
    qual_norm_spec f q (Tqualified q' t') ret
  .
  #[local] Hint Constructors qual_norm_spec : core.

  Lemma qual_norm'_ok f q t : qual_norm_spec f q t (qual_norm' f q t).
  Proof.
    move: q. induction t; intros.
    all: rewrite qual_norm'_unfold; auto.
  Qed.

  Lemma qual_norm'_unqual f q t : ~~ is_qualified t -> qual_norm' f q t = f q t.
  Proof.
    intros. rewrite qual_norm'_unfold. by destruct t.
  Qed.

  Lemma qual_norm'_idemp f q t : qual_norm' (qual_norm' f) q t = qual_norm' f q t.
  Proof.
    induction (qual_norm'_ok f q t).
    { by rewrite !qual_norm'_unqual. }
    { done. }
  Qed.

  (** [qual_norm] *)

  Lemma qual_norm_unfold f t :
    qual_norm f t =
      if t is Tqualified q' t'
      then qual_norm' f q' t'
      else f QM t.
  Proof.
    rewrite /qual_norm qual_norm'_unfold. f_equiv.
    by rewrite left_id_L.
  Qed.

  Lemma qual_norm_ok f t : qual_norm_spec f QM t (qual_norm f t).
  Proof. apply qual_norm'_ok. Qed.

  Lemma qual_norm_unqual f t : ~~ is_qualified t -> qual_norm f t = f QM t.
  Proof. apply qual_norm'_unqual. Qed.

  Lemma qual_norm_idemp f t : qual_norm (qual_norm' f) t = qual_norm f t.
  Proof. apply qual_norm'_idemp. Qed.
End qual_norm.

Lemma qual_norm'_bind {A B} (f : type_qualifiers -> type -> A) (g : A -> B) q t :
  g (qual_norm' f q t) = qual_norm' (fun q => g ∘ f q) q t.
Proof.
  induction (qual_norm'_ok f q t).
  { by rewrite qual_norm'_unqual. }
  { done. }
Qed.
Lemma qual_norm_bind {A B} (f : type_qualifiers -> type -> A) (g : A -> B) t :
  g (qual_norm f t) = qual_norm (fun q => g ∘ f q) t.
Proof. apply qual_norm'_bind. Qed.

Lemma qual_norm'_equiv q t : qual_norm' Tqualified q t ≡ Tqualified q t.
Proof.
  induction (qual_norm'_ok Tqualified q t).
  { done. }
  { by rewrite Tqualified_merge. }
Qed.
Lemma qual_norm_equiv t : qual_norm Tqualified t ≡ t.
Proof. by rewrite /qual_norm qual_norm'_equiv Tqualified_id. Qed.

(** [decompose_type] *)

Lemma decompose_type_unfold t :
  decompose_type t =
    if t is Tqualified q t' then
      let p := decompose_type t' in
      (merge_tq q p.1, p.2)
    else (QM, t).
Proof.
  rewrite /decompose_type qual_norm_unfold.
  destruct t; try done. set pair := fun x y => (x, y).
  move: q. induction t=>?; cbn; try by rewrite right_id_L.
  rewrite left_id_L !IHt /=. f_equal. by rewrite assoc_L.
Qed.

Inductive decompose_type_spec : type -> type_qualifiers * type -> Prop :=
| decompose_type_spec_unqual t : ~~ is_qualified t -> decompose_type_spec t (QM, t)
| decompose_type_spec_qual q t p :
  decompose_type_spec t p ->
  decompose_type_spec (Tqualified q t) (merge_tq q p.1, p.2)
.
#[local] Hint Constructors decompose_type_spec : core.

Lemma decompose_type_ok t : decompose_type_spec t (decompose_type t).
Proof.
  induction t.
  all: rewrite decompose_type_unfold; cbn; auto.
Qed.

Lemma is_qualified_decompose_type t : ~~ is_qualified (decompose_type t).2.
Proof. by induction (decompose_type_ok t). Qed.

Lemma decompose_type_unqual t : ~~ is_qualified t -> decompose_type t = (QM, t).
Proof. apply qual_norm_unqual. Qed.

Lemma decompose_type_qual q t :
  decompose_type (Tqualified q t) =
    let p := decompose_type t in
    (merge_tq q p.1, p.2).
Proof. by rewrite decompose_type_unfold. Qed.

Lemma decompose_type_idemp t :
  decompose_type (decompose_type t).2 = (QM, (decompose_type t).2).
Proof. rewrite decompose_type_unqual; eauto using is_qualified_decompose_type. Qed.

Lemma decompose_type_equiv t : let p := decompose_type t in Tqualified p.1 p.2 ≡ t.
Proof.
  elim: (decompose_type_ok t); cbn.
  { intros. by rewrite Tqualified_id. }
  { intros ???? <-. by rewrite Tqualified_merge. }
Qed.

(** [qual_norm], [qual_norm'] in terms of [decompose_type] *)

Lemma qual_norm'_decompose_type {A} (f : type_qualifiers -> type -> A) q t :
  qual_norm' f q t =
    let p := decompose_type t in
    f (merge_tq q p.1) p.2.
Proof.
  move: q. induction t=>? /=; try by rewrite right_id_L.
  rewrite decompose_type_unfold IHt /=. by rewrite assoc_L.
Qed.

Lemma qual_norm_decompose_type {A} (f : type_qualifiers -> type -> A) t :
  qual_norm f t =
    let p := decompose_type t in
    f p.1 p.2.
Proof.
  rewrite /qual_norm qual_norm'_decompose_type. cbn.
  by rewrite left_id_L.
Qed.

(** [drop_qualifiers] *)

Lemma is_qualified_drop_qualifiers ty : ~~ is_qualified (drop_qualifiers ty).
Proof. by induction ty. Qed.
#[local] Hint Resolve is_qualified_drop_qualifiers | 0 : core. (* TODO: make this global? *)

Lemma drop_qualifiers_unqual t : ~~ is_qualified t -> drop_qualifiers t = t.
Proof. by destruct t; cbn; auto. Qed.

Lemma drop_qualifiers_qual_norm' q t : drop_qualifiers t = qual_norm' (fun _ t => t) q t.
Proof.
  elim: (qual_norm'_ok _ q t).
  { intros. by rewrite drop_qualifiers_unqual. }
  { done. }
Qed.
Lemma drop_qualifiers_qual_norm t : drop_qualifiers t = qual_norm (fun _ t => t) t.
Proof. apply drop_qualifiers_qual_norm'. Qed.
Lemma drop_qualifiers_decompose_type t : drop_qualifiers t = (decompose_type t).2.
Proof. by rewrite drop_qualifiers_qual_norm qual_norm_decompose_type. Qed.

Lemma drop_qualifiers_idemp t : drop_qualifiers (drop_qualifiers t) = drop_qualifiers t.
Proof. by rewrite drop_qualifiers_unqual. Qed.

Lemma unqual_drop_qualifiers ty tq ty' : drop_qualifiers ty <> Tqualified tq ty'.
Proof. by induction ty. Qed.

Variant qual_norm_decomp_spec {A} (f : type_qualifiers → type → A) t : A -> Prop :=
| QualNormDecomp q' t' : (q', t') = decompose_type t -> qual_norm_decomp_spec f t (f q' t')
.

Lemma qual_norm_decomp_ok {A} (f : type_qualifiers → type → A) t : qual_norm_decomp_spec f t (qual_norm f t).
Proof.
  rewrite qual_norm_decompose_type.
  by constructor; rewrite -?surjective_pairing -?drop_qualifiers_decompose_type.
Qed.

(** ** Erasing qualifiers *)
(**
[erase_qualifiers t] erases *all* qualifiers that occur everywhere in
the type.

NOTE we currently use this because we do not track [const]ness in the
logic, this is somewhat reasonable because we often opt to express
this in separation logic. And the type system also enforces some of
the other criteria.
*)
Fixpoint erase_qualifiers (t : type) : type :=
  match t with
  | Tptr t => Tptr (erase_qualifiers t)
  | Tref t => Tref (erase_qualifiers t)
  | Trv_ref t => Trv_ref (erase_qualifiers t)
  | Tnum _ _
  | Tchar_ _
  | Tbool
  | Tvoid
  | Tfloat_ _
  | Tnamed _
  | Tenum _ => t
  | Tarray t sz => Tarray (erase_qualifiers t) sz
  | Tincomplete_array t => Tincomplete_array (erase_qualifiers t)
  | Tvariable_array t e => Tvariable_array (erase_qualifiers t) e
  | Tfunction ft => Tfunction $ FunctionType (ft_cc:=ft.(ft_cc)) (ft_arity:=ft.(ft_arity)) (erase_qualifiers ft.(ft_return)) (List.map erase_qualifiers ft.(ft_params))
  | Tmember_pointer cls t => Tmember_pointer cls (erase_qualifiers t)
  | Tqualified _ t => erase_qualifiers t
  | Tnullptr => Tnullptr
  | Tarch sz nm => Tarch sz nm
  | Tunsupported msg => Tunsupported msg
  | Tparam _
  | Tresult_param _
  | Tresult_global _
  | Tresult_unop _ _ | Tresult_binop _ _ _ | Tresult_call _ _ | Tresult_member_call _ _ _
  | Tresult_parenlist _ _
  | Tresult_member _ _
  | Tauto
  | Tdecltype _ => t (* TODO: it isn't clear what [erase_qualifiers] means on meta types *)
  | Texprtype _ => t (* TODO: it isn't clear what [erase_qualifiers] means on meta types *)
  end.

Lemma is_qualified_erase_qualifiers ty : ~~ is_qualified (erase_qualifiers ty).
Proof. by induction ty. Qed.
#[local] Hint Resolve is_qualified_erase_qualifiers | 0 : core. (* TODO: global *)

Lemma erase_qualifiers_qual_norm' q t :
  erase_qualifiers t = qual_norm' (fun _ t => erase_qualifiers t) q t.
Proof. by elim: (qual_norm'_ok _ q t). Qed.
Lemma erase_qualifiers_qual_norm t :
  erase_qualifiers t = qual_norm (fun _ t => erase_qualifiers t) t.
Proof. apply erase_qualifiers_qual_norm'. Qed.
Lemma erase_qualifiers_decompose_type t :
  erase_qualifiers t = erase_qualifiers (decompose_type t).2.
Proof. by rewrite erase_qualifiers_qual_norm qual_norm_decompose_type. Qed.

Lemma erase_qualifiers_idemp t : erase_qualifiers (erase_qualifiers t) = erase_qualifiers t.
Proof.
  move: t. fix IHt 1=>t.
  destruct t; cbn; auto with f_equal.
  { (* functions *) rewrite IHt. f_equal. f_equal. induction (ft_params t); cbn; auto with f_equal. }
Qed.

Lemma drop_erase_qualifiers t : drop_qualifiers (erase_qualifiers t) = erase_qualifiers t.
Proof. by rewrite drop_qualifiers_unqual. Qed.
Lemma erase_drop_qualifiers t : erase_qualifiers (drop_qualifiers t) = erase_qualifiers t.
Proof. induction t; cbn; auto. Qed.

#[deprecated(since="20230531", note="Use [drop_erase_qualifiers].")]
Notation drop_erase := drop_erase_qualifiers.
#[deprecated(since="20230531", note="Use [erase_drop_qualifiers].")]
Notation erase_drop := drop_erase_qualifiers.

Lemma unqual_erase_qualifiers ty tq ty' : erase_qualifiers ty <> Tqualified tq ty'.
Proof. by induction ty. Qed.

(** ** Qualifier simplification tactic *)
(* Lemmas for all [type] constructors; in constructor order for easy review. *)
Lemma drop_qualifiers_Tptr : forall [ty ty'],
    drop_qualifiers ty = Tptr ty' -> erase_qualifiers ty = Tptr (erase_qualifiers ty').
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Tref : forall [ty ty'],
    drop_qualifiers ty = Tref ty' -> erase_qualifiers ty = Tref (erase_qualifiers ty').
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Trv_ref : forall [ty ty'],
    drop_qualifiers ty = Trv_ref ty' -> erase_qualifiers ty = Trv_ref (erase_qualifiers ty').
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Tnum : forall [ty sz sgn],
    drop_qualifiers ty = Tnum sz sgn -> erase_qualifiers ty = Tnum sz sgn.
Proof. by induction ty. Qed.
Lemma drop_qualifiers_Tchar_ : forall [ty ct],
    drop_qualifiers ty = Tchar_ ct -> erase_qualifiers ty = Tchar_ ct.
Proof. by induction ty. Qed.
Lemma drop_qualifiers_Tvoid : forall [ty],
    drop_qualifiers ty = Tvoid -> erase_qualifiers ty = Tvoid.
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Tarray : forall [ty ty' n],
    drop_qualifiers ty = Tarray ty' n -> erase_qualifiers ty = Tarray (erase_qualifiers ty') n.
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Tnamed : forall [ty n],
    drop_qualifiers ty = Tnamed n -> erase_qualifiers ty = Tnamed n.
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Tenum : forall [ty nm],
    drop_qualifiers ty = Tenum nm -> erase_qualifiers ty = Tenum nm.
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Tfunction : forall [ty c ar ty' tArgs],
    drop_qualifiers ty = Tfunction (@FunctionType _ c ar ty' tArgs) ->
    erase_qualifiers ty = Tfunction (@FunctionType _ c ar (erase_qualifiers ty') (map erase_qualifiers tArgs)).
Proof. induction ty; simpl; intros; try congruence; eauto. inversion H; subst. done. Qed.
Lemma drop_qualifiers_Tbool : forall [ty],
    drop_qualifiers ty = Tbool -> erase_qualifiers ty = Tbool.
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Tmember_pointer : forall [ty cls ty'],
    drop_qualifiers ty = Tmember_pointer cls ty' ->
    erase_qualifiers ty = Tmember_pointer cls (erase_qualifiers ty').
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
Lemma drop_qualifiers_Tfloat : forall [ty sz],
    drop_qualifiers ty = Tfloat_ sz -> erase_qualifiers ty = Tfloat_ sz.
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.
(* Omit Tqualified on purpose *)
Lemma drop_qualifiers_Tnullptr : forall [ty],
    drop_qualifiers ty = Tnullptr -> erase_qualifiers ty = Tnullptr.
Proof. induction ty; simpl; intros; try congruence; eauto. Qed.

(** simplify instances where you have [drop_qualifiers ty = Txxx ..]
    for some [Txxx]. *)
(* Same order as above, for easier review. *)
Ltac simpl_drop_qualifiers :=
  match goal with
  | H : drop_qualifiers _ = _ |- _ => first
          [ rewrite (drop_qualifiers_Tptr H)
          | rewrite (drop_qualifiers_Tref H)
          | rewrite (drop_qualifiers_Trv_ref H)
          | rewrite (drop_qualifiers_Tnum H)
          | rewrite (drop_qualifiers_Tchar_ H)
          | rewrite (drop_qualifiers_Tvoid H)
          | rewrite (drop_qualifiers_Tarray H)
          | rewrite (drop_qualifiers_Tnamed H)
          | rewrite (drop_qualifiers_Tenum H)
          | rewrite (drop_qualifiers_Tfunction H)
          | rewrite (drop_qualifiers_Tbool H)
          | rewrite (drop_qualifiers_Tmember_pointer H)
          | rewrite (drop_qualifiers_Tfloat H)
          | rewrite (drop_qualifiers_Tnullptr H)
          ]
  end.

(**
[is_ref t] decides if [t] a reference type

Note: [is_ref] is incompatible with the equivalence on types.
Counterexample: [Tqualified QM (Tref t) ≡ Tref t].
*)
Definition is_ref (t : type) : bool :=
  if t is (Tref _ | Trv_ref _) then true else false.

Lemma is_ref_spec t : is_ref t <-> ∃ t', t = Tref t' \/ t = Trv_ref t'.
Proof. split=>Href. by destruct t; eauto. by destruct Href as (?&[-> | ->]). Qed.

Lemma is_ref_unqualified t : is_ref t -> ~~ is_qualified t.
Proof. by destruct t. Qed.

Lemma is_ref_drop_qualifiers t : is_ref t -> is_ref (drop_qualifiers t).
Proof. by destruct t. Qed.

(**
[is_QM cv] decides if [cv] is the neutral qualifier [QM]
*)
Definition is_QM (cv : type_qualifiers) : bool :=
  if cv is QM then true else false.

Lemma is_QM_spec cv : is_QM cv <-> cv = QM.
Proof. by destruct cv. Qed.
Lemma is_QM_bool_decide cv : is_QM cv = bool_decide (cv = QM).
Proof. by destruct cv. Qed.

(** [tqualified] *)

Variant tqualified'_spec : type_qualifiers -> type -> type -> Prop :=
| tqualified'_spec_ref q t : is_ref t -> tqualified'_spec q t t
| tqualified'_spec_unqual t : ~~ is_ref t -> tqualified'_spec QM t t
| tqualified'_spec_qual q t : ~~ is_ref t -> ~~ is_QM q -> tqualified'_spec q t (Tqualified q t)
.
#[local] Hint Constructors tqualified'_spec : core.

Lemma tqualified'_ok q t : tqualified'_spec q t (tqualified' q t).
Proof.
  rewrite /tqualified'. destruct (boolP (is_ref t)); [by destruct t; auto|].
  destruct t; try done.
  all: destruct (boolP (is_QM q)); by destruct q; auto.
Qed.

Lemma tqualified'_equiv q t : tqualified' q t ≡ Tqualified q t.
Proof.
  case: (tqualified'_ok q t).
  { intros ?? (?&[-> | ->])%is_ref_spec.
    by rewrite Tqualified_ref. by rewrite Tqualified_rv_ref. }
  { intros. by rewrite Tqualified_id. }
  { done. }
Qed.

#[global] Instance: Params (@tqualified') 1 := {}.
#[global] Instance tqualified'_proper q : Proper (equiv ==> equiv) (tqualified' q).
Proof. intros t1 t2 Ht. by rewrite !tqualified'_equiv Ht. Qed.

Lemma tqualified'_ref q t : is_ref t -> tqualified' q t = t.
Proof. by destruct t. Qed.

Lemma tqualified'_QM t : tqualified' QM t = t.
Proof. by destruct t. Qed.

Lemma tqualified'_non_ref q t : ~~ is_ref t -> ~~ is_QM q -> tqualified' q t = Tqualified q t.
Proof. by destruct t, q. Qed.

Lemma tqualified_ok q t : qual_norm_spec tqualified' q t (tqualified q t).
Proof. apply qual_norm'_ok. Qed.

Lemma tqualified_equiv q t : tqualified q t ≡ Tqualified q t.
Proof.
  induction (tqualified_ok q t).
  { by rewrite tqualified'_equiv. }
  { by rewrite Tqualified_merge. }
Qed.

#[global] Instance: Params (@tqualified) 1 := {}.
#[global] Instance tqualified_proper q : Proper (equiv ==> equiv) (tqualified q).
Proof. intros t1 t2 Ht. by rewrite !tqualified_equiv Ht. Qed.

Lemma tqualified_tqualified' q t : tqualified q t ≡ tqualified' q t.
Proof. by rewrite tqualified_equiv tqualified'_equiv. Qed.

Lemma tqualified_qual_norm' q t : tqualified q t = qual_norm' tqualified' q t.
Proof. done. Qed.

Lemma tqualified_decompose_type q t :
  tqualified q t =
    let p := decompose_type t in
    tqualified' (merge_tq q p.1) p.2.
Proof.
  by rewrite tqualified_qual_norm' qual_norm'_decompose_type.
Qed.

Lemma tqualified_unqual q t : ~~ is_qualified t -> tqualified q t = tqualified' q t.
Proof. intros. by rewrite /tqualified qual_norm'_unqual. Qed.

Lemma tqualified_idemp q1 q2 t :
  tqualified q1 (tqualified q2 t) = tqualified (merge_tq q1 q2) t.
Proof.
  elim: (tqualified_ok q2 t) q1; last first.
  { intros ????? IH ?. rewrite {}IH /=. by rewrite !assoc_L. }
  intros q2' t' ? q1. destruct (tqualified'_ok q2' t').
  - rewrite !tqualified_unqual//. by rewrite !tqualified'_ref.
  - rewrite !tqualified_unqual//. by rewrite right_id_L.
  - done.
Qed.

Lemma drop_qualifiers_tqualified q t :
  drop_qualifiers (tqualified q t) = drop_qualifiers t.
Proof.
  induction (tqualified_ok q t).
  { by destruct (tqualified'_ok q t). }
  { done. }
Qed.

Lemma erase_qualifiers_tqualified q t :
  erase_qualifiers (tqualified q t) = erase_qualifiers t.
Proof.
  induction (tqualified_ok q t).
  { by destruct (tqualified'_ok q t). }
  { done. }
Qed.

(** [tref] *)

Inductive tref_spec : type_qualifiers -> type -> type -> Prop :=
| tref_spec_nonref_unqual q t : ~~ is_ref t -> ~~ is_qualified t -> tref_spec q t (Tref $ tqualified q t)
| tref_spec_ref q t ret : tref_spec QM t ret -> tref_spec q (Tref t) ret
| tref_spec_rv_ref q t ret : tref_spec QM t ret -> tref_spec q (Trv_ref t) ret
| tref_spec_qual q q' t ret : tref_spec (merge_tq q q') t ret -> tref_spec q (Tqualified q' t) ret
.
#[local] Hint Constructors tref_spec : core.

Lemma tref_ok q t : tref_spec q t (tref q t).
Proof. revert q. induction t; auto. Qed.

Lemma tref_nonref_unqual cv (t : type) :
  ~~ is_ref t -> ~~ is_qualified t -> tref cv t = Tref $ tqualified cv t.
Proof. by destruct t. Qed.

(*
Lemma tref_equiv' q t : tref q t ≡ Tref (Tqualified q t).
Proof.
  elim: (tref_ok q t).
  { intros. by rewrite tqualified_equiv. }
  { intros ???? ->. by rewrite Tqualified_id Tqualified_ref Tref_ref. }
  { intros ???? ->. by rewrite Tqualified_id Tqualified_rv_ref Tref_rv_ref. }
  { intros. by rewrite Tqualified_merge. }
Qed.
Lemma tref_equiv t : tref QM t ≡ Tref t.
Proof. by rewrite tref_equiv' Tqualified_id. Qed.

#[global] Instance: Params (@tref) 1 := {}.
#[global] Instance tref_proper q : Proper (equiv ==> equiv) (tref q).
Proof. intros t1 t2 Ht. by rewrite !tref_equiv' Ht. Qed.
*)

Lemma tref_unfold q t :
  tref q t =
    qual_norm' (fun q' t' =>
      match t' with
      | Tref t'' | Trv_ref t'' => tref QM t''
      | _ => Tref (tqualified q' t')
      end
    ) q t.
Proof. move: q. by induction t; cbn. Qed.

(** [trv_ref] *)

Inductive trv_ref_spec : type_qualifiers -> type -> type -> Prop :=
| trv_ref_spec_nonref_unqual q t : ~~ is_ref t -> ~~ is_qualified t -> trv_ref_spec q t (Trv_ref $ tqualified q t)
| trv_ref_spec_ref q t : trv_ref_spec q (Tref t) (tref QM t)
| trv_ref_spec_rv_ref q t ret : trv_ref_spec QM t ret -> trv_ref_spec q (Trv_ref t) ret
| trv_ref_spec_qual q q' t ret : trv_ref_spec (merge_tq q q') t ret -> trv_ref_spec q (Tqualified q' t) ret
.
#[local] Hint Constructors trv_ref_spec : core.

Lemma trv_ref_ok q t : trv_ref_spec q t (trv_ref q t).
Proof. revert q; induction t; auto. Qed.

Lemma trv_ref_nonref_unqual cv (t : type) :
  ~~ is_ref t -> ~~ is_qualified t -> trv_ref cv t = Trv_ref $ tqualified cv t.
Proof. by destruct t. Qed.

(*
Lemma trv_ref_equiv' q t : trv_ref q t ≡ Trv_ref (Tqualified q t).
Proof.
  elim: (trv_ref_ok q t).
  { intros. by rewrite tqualified_equiv. }
  { intros. by rewrite tref_equiv' Tqualified_id Tqualified_ref Trv_ref_ref. }
  { intros ???? ->. by rewrite Tqualified_id Tqualified_rv_ref Trv_ref_rv_ref. }
  { intros. by rewrite Tqualified_merge. }
Qed.
Lemma trv_ref_equiv t : trv_ref QM t ≡ Trv_ref t.
Proof. by rewrite trv_ref_equiv' Tqualified_id. Qed.

#[global] Instance: Params (@trv_ref) 1 := {}.
#[global] Instance trv_ref_proper q : Proper (equiv ==> equiv) (trv_ref q).
Proof. intros t1 t2 Ht. by rewrite !trv_ref_equiv' Ht. Qed.
*)

Lemma trv_ref_unfold q t :
  trv_ref q t =
    qual_norm' (fun q' t' =>
      match t' with
      | Tref t'' => tref QM t''
      | Trv_ref t'' => trv_ref QM t''
      | _ => Trv_ref (tqualified q' t')
      end
    ) q t.
Proof. move: q. by induction t; cbn. Qed.

(** ** Type normalization *)

Definition to_arg_type : type -> type :=
  qual_norm (fun cv t =>
               match t with
               | Tarray ety _
               | Tvariable_array ety _
               | Tincomplete_array ety => Tptr ety
               | _ => t (* the outer qualifiers do not factor into the type *)
               end).

Lemma to_arg_type_idempotent : forall t, to_arg_type (to_arg_type t) = to_arg_type t.
Proof.
  rewrite /to_arg_type/=/qual_norm/=. intro t.
  rewrite !qual_norm'_decompose_type.
  destruct (decompose_type t) eqn:Heq.
  simpl. destruct t1; simpl; eauto.
  exfalso.
  generalize (is_qualified_decompose_type t). rewrite Heq. auto.
Qed.


(**
normalization of types
- compresses adjacent [Tqualified] constructors
- drops (irrelevant) qualifiers on function arguments
 *)
Fixpoint normalize_type' (cv : type_qualifiers) (t : type) : type :=
  let normalize_type := normalize_type' QM in
  match t with
  | Tptr t => tqualified cv $ Tptr (normalize_type t)
  | Tref t => Tref (normalize_type t)
  | Trv_ref t => Trv_ref (normalize_type t)
  | Tarray t n => Tarray (normalize_type' cv t) n
  | Tincomplete_array t => Tincomplete_array (normalize_type' cv t)
  | Tvariable_array t e => Tvariable_array (normalize_type' cv t) e
  | Tfunction ft =>
    Tfunction $ FunctionType (ft_cc:=ft.(ft_cc)) (ft_arity:=ft.(ft_arity))
      (normalize_type ft.(ft_return))
      (List.map (fun t => to_arg_type $ normalize_type' QM t) ft.(ft_params))
  | Tmember_pointer gn t => Tmember_pointer gn (normalize_type t)
  | Tqualified q t => normalize_type' (merge_tq cv q) t
  | Tnum _ _
  | Tchar_ _
  | Tbool
  | Tvoid
  | Tnamed _
  | Tenum _
  | Tnullptr
  | Tfloat_ _
  | Tarch _ _ => tqualified cv t
  | Tunsupported _ => tqualified cv t
  | Tparam _
  | Tresult_param _
  | Tresult_global _
  | Tresult_unop _ _ | Tresult_binop _ _ _ | Tresult_call _ _ | Tresult_member_call _ _ _
  | Tresult_parenlist _ _
  | Tresult_member _ _
  | Tauto
  | Tdecltype _ => tqualified cv t
  | Texprtype _ => tqualified cv t
  end.
Notation normalize_type := (normalize_type' QM).

Definition normalize_arg_type (t : type) : type :=
  to_arg_type $ normalize_type t.

Fixpoint normalize_type'_idempotent ty {struct ty}: forall cv1 cv2,
  normalize_type' cv1 (normalize_type' cv2 ty) = normalize_type' (merge_tq cv1 cv2) ty
with to_arg_type_normalize_type'_idempotent ty {struct ty} : forall cv,
  normalize_type' QM (to_arg_type $ normalize_type' cv ty) = to_arg_type (normalize_type' cv ty).
Proof.
  { destruct ty; simpl; try solve [ destruct cv1, cv2; clear; eauto ].
    all: try solve [ intros; f_equal; apply normalize_type'_idempotent ].
    { destruct cv1, cv2; simpl; f_equal; try first [ apply normalize_type'_idempotent
                                                  | f_equal; apply normalize_type'_idempotent ]. }
    { intros. do 2 f_equal. apply normalize_type'_idempotent.
      induction (ft_params t); simpl; f_equal; [ | apply IHl ].
      rewrite to_arg_type_normalize_type'_idempotent.
      by rewrite to_arg_type_idempotent. }
    { intros; rewrite normalize_type'_idempotent.
      by rewrite assoc_L. } }
  { destruct ty; simpl; try solve [ destruct cv; clear; eauto ].
    all: try by destruct cv; rewrite /=/to_arg_type/=/qual_norm/=; rewrite normalize_type'_idempotent.
    all: try by rewrite /=/to_arg_type/=/qual_norm/=; rewrite normalize_type'_idempotent.
    { rewrite /=/to_arg_type/=/qual_norm/=; rewrite normalize_type'_idempotent.
      intros. do 2 f_equal.
      induction (ft_params t); simpl; f_equal; [ | apply IHl ].
      rewrite to_arg_type_normalize_type'_idempotent.
      etrans; [ eapply to_arg_type_idempotent | ]. done. }
    { intros. rewrite to_arg_type_normalize_type'_idempotent. done. } }
Qed.

Lemma normalize_type_idempotent ty : normalize_type (normalize_type ty) = normalize_type ty.
Proof. apply normalize_type'_idempotent. Qed.

Definition normalize_arg_type_idempotent : forall t,
    normalize_arg_type (normalize_arg_type t) = normalize_arg_type t.
Proof.
  by intros; rewrite /normalize_arg_type to_arg_type_normalize_type'_idempotent to_arg_type_idempotent.
Qed.


(** ** Qualifier-aware type operations *)

(**
[unptr t] returns the type of the object that a value of type [t]
points to or [None] if [t] is not a pointer type.
*)
Definition unptr (t : exprtype) : option exprtype :=
  match drop_qualifiers t with
  | Tptr p => Some p
  | _ => None
  end.

(* [array_type t] extracts element type of the array or fails. *)
Definition array_type : exprtype -> option exprtype :=
  qual_norm (fun cv ty =>
               match ty with
               | Tarray ety _
               | Tincomplete_array ety
               | Tvariable_array ety _ => Some $ tqualified cv ety
               | _ => None
               end).

(**
[class_name t] returns the name of the class that this type refers to
*)
Definition class_name (t : type) : option name :=
  match drop_qualifiers t with
  | Tnamed gn => Some gn
  | _ => None
  end.

(**
[is_arithmetic ty] states whether [ty] is an arithmetic type
*)
Definition is_arithmetic (ty : type) : bool :=
  match drop_qualifiers ty with
  | Tnum _ _
  | Tchar_ _
  | Tfloat_ _
  | Tenum _
  | Tbool => true
  | _ => false
  end.

(* [as_function ty] returns the [function_type'] if [ty] is a function type. *)
Definition as_function (ty : functype) : option function_type :=
  match ty with
  | Tfunction ft => Some ft
  | _ => None
  end.

(* extracts the parameter information from a function type *)
Definition args_for (ft : function_type)
  : list decltype * function_arity :=
  (ft.(ft_params), ft.(ft_arity)).

(**
[is_pointer ty] is [true] if [ty] is a pointer type
*)
Definition is_pointer (ty : type) : bool :=
  match drop_qualifiers ty with
  | Tptr _ | Tnullptr => true
  | _ => false
  end.

Lemma is_pointer_not_arithmetic : forall ty, is_pointer ty = true -> is_arithmetic ty = false.
Proof. induction ty; simpl; intros; eauto. Qed.
Lemma is_arithmetic_not_pointer : forall ty, is_arithmetic ty = true -> is_pointer ty = false.
Proof. induction ty; simpl; intros; eauto. Qed.

(**
Formalizes https://eel.is/c++draft/basic.types.general#term.scalar.type.
*)
Definition is_scalar_type (ty : type) : bool :=
  match drop_qualifiers ty with
  | Tnullptr | Tptr _
  | Tmember_pointer _ _
  | Tfloat_ _
  | Tchar_ _
  | Tbool
  | Tnum _ _ | Tenum _ => true
  | _ => false
  end.
Lemma is_scalar_type_erase_drop ty :
  is_scalar_type (erase_qualifiers ty) = is_scalar_type (drop_qualifiers ty).
Proof. by induction ty. Qed.
Lemma is_scalar_type_erase ty :
  is_scalar_type (erase_qualifiers ty) = is_scalar_type ty.
Proof. rewrite /is_scalar_type. induction ty; simpl; auto. Qed.
Lemma is_scalar_type_drop ty :
  is_scalar_type (drop_qualifiers ty) = is_scalar_type ty.
Proof. rewrite /is_scalar_type. induction ty; simpl; auto. Qed.

(**
[is_value_type t] returns [true] if [t] has value semantics. A value
type is one that can be represented by [val].

NOTE: The only difference between a value type and a scalar type is
that [Tvoid] is a value type and not a scalar type.
 *)
Definition is_value_type (t : type) : bool :=
  match drop_qualifiers t with
  | Tnum _ _
  | Tchar_ _
  | Tbool
  | Tptr _
  | Tnullptr
  | Tfloat_ _
  | Tmember_pointer _ _
  (**
  NOTE: In C++ the the underlying type of an enumeration must be an
  integral type. This definition pre-supposes [t] a valid enumeration.
  *)
  | Tenum _ (* enum types are value types *)
  | Tvoid => true
  | _ => false
  end.

Lemma is_value_type_erase_qualifiers ty :
  is_value_type (erase_qualifiers ty) = is_value_type ty.
Proof. induction ty; cbn; auto. Qed.
Lemma is_value_type_drop_qualifiers ty :
  is_value_type (drop_qualifiers ty) = is_value_type ty.
Proof. induction ty; cbn; auto. Qed.

Lemma is_value_type_qual_norm' q t :
  is_value_type t = qual_norm' (fun _ t' => is_value_type t') q t.
Proof. by elim: (qual_norm'_ok _ q t). Qed.
Lemma is_value_type_qual_norm t :
  is_value_type t = qual_norm (fun _ t' => is_value_type t') t.
Proof. apply is_value_type_qual_norm'. Qed.
Lemma is_value_type_decompose_type t :
  is_value_type t = is_value_type (decompose_type t).2.
Proof. by rewrite is_value_type_qual_norm qual_norm_decompose_type. Qed.

(** For use in [init_validR] *)
Fixpoint zero_sized_array ty : bool :=
  qual_norm (fun _ t => match t with
                     | Tarray ety n =>
                         if bool_decide (n = 0%N) then true
                         else zero_sized_array ety
                     | _ => false
                     end) ty.
#[global] Arguments zero_sized_array !_ /.

Lemma zero_sized_array_unfold t : forall q,
    zero_sized_array t =
    qual_norm' (fun _ t =>
                  match t with
                  | Tarray t n => if bool_decide (n = 0%N) then true else zero_sized_array t
                  | _ => false
                  end) q t.
Proof.
  induction t; simpl; intros; auto.
  { rewrite qual_norm_unfold. rewrite /qual_norm/=.
    rewrite -IHt. rewrite {2}/zero_sized_array.
    destruct q0; auto. }
Qed.
Lemma zero_sized_array_erase_qualifiers t :
  zero_sized_array t = zero_sized_array (erase_qualifiers t).
Proof.
  induction t; simpl; auto.
  { rewrite !qual_norm_unfold -IHt. done. }
  { rewrite qual_norm_unfold.
    rewrite -IHt.
    erewrite zero_sized_array_unfold. done. }
Qed.
Lemma zero_sized_array_qual ty : forall t,
    zero_sized_array ty = zero_sized_array (Tqualified t ty).
Proof.
  intros. rewrite (zero_sized_array_erase_qualifiers (Tqualified _ _)) /=.
  apply zero_sized_array_erase_qualifiers.
Qed.


(**
[is_reference_type t] returns [true] if [t] is a (possibly
cv-qualified) reference type.
*)
Definition is_reference_type (t : type) : bool :=
  is_ref (drop_qualifiers t).

Lemma is_ref_incl t : is_ref t -> is_reference_type t.
Proof. apply is_ref_drop_qualifiers. Qed.

Lemma value_type_non_ref {ty} : is_value_type ty -> ~~ is_reference_type ty.
Proof. by induction ty. Qed.

Lemma is_reference_type_erase_qualifiers t :
  is_reference_type (erase_qualifiers t) = is_reference_type t.
Proof. induction t; cbn; auto. Qed.
Lemma is_reference_type_drop_qualifiers t :
  is_reference_type (drop_qualifiers t) = is_reference_type t.
Proof. induction t; cbn; auto. Qed.

Lemma is_reference_type_qual_norm' q t :
  is_reference_type t = qual_norm' (fun _ t => is_reference_type t) q t.
Proof. by elim: (qual_norm'_ok _ q t). Qed.
Lemma is_reference_type_qual_norm t :
  is_reference_type t = qual_norm (fun _ t => is_reference_type t) t.
Proof. apply is_reference_type_qual_norm'. Qed.
Lemma is_reference_type_decompose_type t :
  is_reference_type t = is_reference_type (decompose_type t).2.
Proof. by rewrite is_reference_type_qual_norm qual_norm_decompose_type. Qed.

(**
[as_ref' f x t] applies [f u] if [t] is a (possibly cv-qualified)
reference type with underlying type [u], defaulting to [x] if [t] is
not a reference type.

The special cases [as_ref t : type] and [as_ref_option : option type]
return the underlying type [u] (defaulting, respectively, to a dummy
type and to [None]).
*)

Definition as_ref' {A} (f : exprtype -> A) (x : A) (t : type) : A :=
  if drop_qualifiers t is (Tref u | Trv_ref u) then f u else x.
Notation as_ref := (as_ref' (fun u => u) Tvoid).
Notation as_ref_option := (as_ref' Some None).

Lemma as_ref'_erase_qualifiers {A} (f : exprtype -> A) (x : A) t :
  as_ref' f x (erase_qualifiers t) = as_ref' (f ∘ erase_qualifiers) x t.
Proof. induction t; cbn; auto. Qed.
Lemma as_ref_erase_qualifiers t :
  as_ref (erase_qualifiers t) = erase_qualifiers (as_ref t).
Proof. induction t; cbn; auto. Qed.

Section as_ref'.
  Context {A : Type} (f : exprtype -> A) (x : A).
  #[local] Notation as_ref' := (as_ref' f x).

  Lemma as_ref_drop_qualifiers t : as_ref' (drop_qualifiers t) = as_ref' t.
  Proof. induction t; cbn; auto. Qed.
  Lemma as_ref_qual_norm' q t : as_ref' t = qual_norm' (fun _ t => as_ref' t) q t.
  Proof. by elim: (qual_norm'_ok _ q t). Qed.
  Lemma as_ref_qual_norm t : as_ref' t = qual_norm (fun _ t => as_ref' t) t.
  Proof. apply as_ref_qual_norm'. Qed.
  Lemma as_ref_decompose_type t : as_ref' t = as_ref' (decompose_type t).2.
  Proof. by rewrite as_ref_qual_norm qual_norm_decompose_type. Qed.
End as_ref'.

(**
[is_aggregate_type t] returns [true] if [t] is a (possibly qualified)
<<struct>> type.
*)
Definition is_aggregate_type (ty : type) : bool :=
  match drop_qualifiers ty with
  | Tnamed _ => true
  | _ => false
  end.

Lemma is_aggregate_type_drop_qualifiers ty :
  is_aggregate_type (drop_qualifiers ty) = is_aggregate_type ty.
Proof.
  by rewrite /is_aggregate_type drop_qualifiers_idemp.
Qed.
Lemma is_aggregate_type_erase_qualifiers ty :
  is_aggregate_type (erase_qualifiers ty) = is_aggregate_type ty.
Proof. by induction ty. Qed.

Lemma is_aggregate_type_qual_norm' cv ty :
  is_aggregate_type ty = qual_norm' (fun _ ty' => is_aggregate_type ty') cv ty.
Proof. by elim: (qual_norm'_ok _ _ _). Qed.
Lemma is_aggregate_type_qual_norm ty :
  is_aggregate_type ty = qual_norm (fun _ ty' => is_aggregate_type ty')  ty.
Proof. apply is_aggregate_type_qual_norm'. Qed.
Lemma is_aggregate_type_decompose_type ty :
  is_aggregate_type ty = is_aggregate_type (decompose_type ty).2.
Proof.
  by rewrite is_aggregate_type_qual_norm qual_norm_decompose_type.
Qed.

Lemma aggregate_type_non_ref ty : is_aggregate_type ty -> ~~ is_reference_type ty.
Proof. by induction ty. Qed.
Lemma aggregate_type_non_val ty : is_aggregate_type ty -> ~~ is_value_type ty.
Proof. by induction ty. Qed.

Lemma decompose_type_erase_qualifiers ty
  : decompose_type (erase_qualifiers ty) = (QM, erase_qualifiers ty).
Proof.
  induction ty; simpl; intros; eauto.
Qed.

(** Determine if <<ty>> is an array type. *)
Definition is_array_type (ty : type) : bool :=
  match ty with
  | Tarray _ _ | Tincomplete_array _ | Tvariable_array _ _ => true
  | _ => false
  end.

(**
[drop_reference] removes any leading reference types.
*)
Fixpoint drop_reference (t : type) : exprtype :=
  match drop_qualifiers t with
  | Tref u | Trv_ref u => drop_reference u
  | _ => t	(* We do not normalize qualifiers here to promote sharing *)
  end.

Succeed Example TEST_drop_reference : drop_reference (Tconst Tint) = Tconst Tint := eq_refl.
Succeed Example TEST_drop_reference : drop_reference (Tconst (Tref Tint)) = Tint := eq_refl.
Succeed Example TEST_drop_reference : drop_reference (Tconst (Tref (Tconst Tint))) = Tconst Tint := eq_refl.

Lemma drop_reference_ref (t : type) u :
  drop_qualifiers t = Tref u -> drop_reference t = drop_reference u.
Proof.
  destruct t; first [done|cbn].
  { (* [Tref] *) by move=>[->]. }
  { (* [Tqualified] *) by move=>->. }
Qed.

Lemma drop_reference_rv_ref (t : type) u :
  drop_qualifiers t = Trv_ref u -> drop_reference t = drop_reference u.
Proof.
  destruct t; first [done|cbn].
  { (* [Trv_ref] *) by move=>[->]. }
  { (* [Tqualified] *) by move=>->. }
Qed.

Lemma drop_reference_non_ref (t : type) u :
  drop_qualifiers t = u -> ~~ is_ref u -> drop_reference t = t.
Proof.
  move=><-. destruct t; first [done|cbn]. by case_match.
Qed.

(** ** Heap Types

    The C++ memory is typed, but loosely so with respect to cv-qualifiers.
    For example, the C++ runtime invariant does *not* guarantee that a value
    stored in a memory cell of type <<int*>> points to a memory cell that is
    mutable. Generally, this will be true, but constructs such as
    <<const_cast<>>> and casting through pointers explicitly circumvent this.
    To track this, the C++ abstract machine tracks locations with "heap types"
    which are [decltype]s with all qualifiers erased and top-level references
    normalized to [Tref].

    Concrete examples of the above are:
    - <<const int x = 1>>           -- [tptsto "int" 1$c _ 1]
    - <<const int* x = nullptr>>    -- [tptsto "int*" 1$m _ nullptr]
    - <<int* const x = nullptr>>    -- [tptsto "int*" 1$c _ nullptr]
    - <<volatile int x = 0>>        -- not represted using [tptsto]
    - <<volatile int* p = nullptr>> -- [tptsto "int*" 1$m _ nullptr]
    - <<int&& r = ..>>              -- [tptsto "int&" 1$m _ _]
 *)
Definition heap_type : Set := type.
Definition is_heap_type (t : type) : bool :=
     bool_decide (t = erase_qualifiers t)
  && (is_value_type t || match t with
                        | Tref _ => true
                        | _ => false
                        end).

(* get the [heap_type] representation of the given type *)
Definition to_heap_type (t : type) : heap_type :=
  match erase_qualifiers t with
  | Trv_ref t => Tref t
  | t => t
  end.
Lemma to_heap_type_qualified cv t :
  to_heap_type (Tqualified cv t) = to_heap_type t.
Proof. done. Qed.

Lemma heap_type_not_qualified cv t : is_heap_type (Tqualified cv t) -> False.
Proof.
  rewrite /is_heap_type. case_bool_decide => /=; eauto.
  exfalso; eapply unqual_erase_qualifiers; eauto.
Qed.

Definition is_volatile : type -> bool :=
  qual_norm (fun cv _ => q_volatile cv).

(* [Tmember_func ty fty] constructs the function type for a
     member function that takes a [this] parameter of [ty]

   TODO technically the [this] parameter is [const].
 *)
Definition Tmember_func (ty : exprtype) (fty : functype) : functype :=
  match fty with
  | Tfunction ft => Tfunction $ {| ft_cc := ft.(ft_cc) ; ft_arity := ft.(ft_arity)
                                ; ft_return := ft.(ft_return) ; ft_params := Tptr ty :: ft.(ft_params) |}
  | _ => fty
  end.
End with_lang.

Notation normalize_type := (normalize_type' QM).
Notation as_ref := (as_ref' (fun u => u) Tvoid).
Notation as_ref_option := (as_ref' Some None).
#[global] Hint Resolve is_qualified_decompose_type | 0 : core.
#[global] Hint Resolve is_qualified_drop_qualifiers | 0 : core.

(* Deprecations *)
#[global,deprecated(note="use [is_scalar_type].",since="20250203")]
Notation scalar_type := is_scalar_type (only parsing).
