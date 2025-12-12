(*
 * Copyright (c) 2020-2022 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export iris.bi.bi.
(* This export ensures that [upredI] is registered as a canonical structure everywhere. *)
Require Export iris.base_logic.bi.
Require Import iris.proofmode.classes.
Require Export bluerock.prelude.base.
Require Export bluerock.prelude.gmap.
Require Export bluerock.prelude.letstar.
Require Export bluerock.prelude.list_numbers.
Require Export bluerock.iris.extra.bi.only_provable.
Require Export bluerock.iris.extra.bi.derived_laws.

#[global] Instance into_pure_emp PROP : IntoPure (PROP := PROP) emp True.
Proof. by rewrite /IntoPure (bi.pure_intro True emp). Qed.

#[global] Hint Opaque uPred_emp : typeclass_instances.

(** * Notation for functions in the Iris scope. To upstream,
per https://gitlab.mpi-sws.org/iris/iris/-/issues/320. *)
Notation "'λI' x .. y , t" := (fun x => .. (fun y => t%I) ..)
  (at level 200, x binder, y binder, right associativity,
  only parsing) : function_scope.

(* ASCII variant. *)
Notation "'funI' x .. y => t" := (fun x => .. (fun y => t%I) ..)
  (at level 200, x binder, y binder, right associativity,
  only parsing) : function_scope.

(* Variant of [let*] (from [bluerock.prelude.letstar]) for the Iris scope. *)
Notation "'letI*' x , .. , z := t 'in' f" :=
  (t (funI x => .. (funI z => f) ..))
    (only parsing, at level 200, x closed binder, z closed binder) : bi_scope.
Notation "'letI*' := t 'in' f" := (t f%I) (only parsing, at level 200) : bi_scope.

(* ASCII alias for [bi_pure] notation [⌜P⌝]. *)
Notation "[! P !]" := (bi_pure P%type%stdpp) (only parsing) : bi_scope.

(* Avoid some [%I] annotations; this is a workaround for issues with scopes and if, functions, etc. *)
Notation "'emp'" := (bi_emp) : stdpp_scope.

(* Old, pre-Iris notations *)
Notation lentails := (bi_entails) (only parsing).
Notation lequiv := (≡) (only parsing).
Notation ltrue := (True%I) (only parsing).
Notation lfalse := (False%I) (only parsing).
Notation land := (bi_and) (only parsing).
Notation lor := (bi_or) (only parsing).
Notation limpl := (bi_impl) (only parsing).
Notation lforall := (bi_forall) (only parsing).
Notation lexists := (bi_exist) (only parsing).

Ltac split' := intros; apply (anti_symm (⊢)).

(** For [bi] constructors like [monPredI], as opposed to [monPred] *)
Declare Scope bi_type_scope.
Delimit Scope bi_type_scope with bi_type.

(* Charge notation levels *)
Module ChargeNotation.

  Notation "P |-- Q"  := (P%I ⊢ Q%I) (at level 80, no associativity).
  Notation "P '|-@{' PROP } Q" := (P%I ⊢@{PROP} Q%I)
    (at level 80, no associativity, only parsing).

  Notation "P //\\ Q"   := (bi_and P Q) (at level 75, right associativity).
  Notation "P \\// Q"   := (bi_or P Q) (at level 76, right associativity).
  Notation "P -->> Q"   := (bi_impl P Q) (at level 77, right associativity).
  Notation "'Forall' x .. y , p" :=
    (bi_forall (fun x => .. (bi_forall (funI y => p)) ..)) (at level 78, x binder, y binder, right associativity).

  Notation "'Exists' x .. y , p" :=
    (bi_exist (fun x => .. (bi_exist (funI y => p)) ..)) (at level 78, x binder, y binder, right associativity).

  Notation "|--  P" := (⊢ P%I) (at level 85, no associativity).
  Notation "'|-@{' PROP } P" := (⊢@{PROP} P%I)
    (at level 85, no associativity, only parsing).

  Notation "P ** Q" := (bi_sep P Q) (at level 58, right associativity).
  Notation "P -* Q" := (bi_wand P Q) (at level 60, right associativity).

  (* Notation "'|>' P" := (▷  P)%I (at level 71). *)
  Notation "|> P" := (bi_later P) (at level 20, right associativity).

  Notation "P -|- Q"  := (P ⊣⊢ Q) (at level 85, no associativity).
  Notation "P '-|-@{' PROP } Q"  := (P%I ⊣⊢@{PROP} Q%I)
    (at level 85, no associativity, only parsing).

End ChargeNotation.

(** ** Big op notation *)
(*
 * Iris big ops look horrible when formatting boxes overflow: Things
 * shift far to the right. We therefore disable the Iris notation for
 * printing by redeclaring it parsing only, and define our own
 * notation (which includes an optional break after binders---see
 * [../../prelude/reserved_notation.v]).
 *
 * Quoting TFM: "If a notation to be used both for parsing and
 * printing is overridden, both the parsing and printing are
 * invalided, even if the overriding rule is only parsing."
 *
 * On Coq 8.13.2, it seems we need not disable printing for Iris
 * notation. Rather, that version of Coq seems to print a term using
 * the last registered notation. Were this documented as Coq's
 * intended behavior, we could drop all of the "only parsing"
 * declarations that follow.
 *)

(** Big separating conjunction *)

Notation "'[∗' 'list]' i ↦ x ∈ l , P" := (big_opL bi_sep (λ i x, P) l) (only parsing) : bi_scope.
Notation "'[**' 'list]' i |-> x ∈ l , P" := (big_opL bi_sep (λ i x, P) l) : bi_scope.

Notation "'[∗' 'list]' x ∈ l , P" := (big_opL bi_sep (λ _ x, P) l) (only parsing) : bi_scope.
Notation "'[**' 'list]' x ∈ l , P" := (big_opL bi_sep (λ _ x, P) l) : bi_scope.

Notation "'[∗' 'map]' k ↦ x ∈ m , P" := (big_opM bi_sep (λ k x, P) m) (only parsing) : bi_scope.
Notation "'[**' 'map]' k |-> x ∈ m , P" := (big_opM bi_sep (λ k x, P) m) : bi_scope.

Notation "'[∗' 'map]' x ∈ m , P" := (big_opM bi_sep (λ _ x, P) m) (only parsing) : bi_scope.
Notation "'[**' 'map]' x ∈ m , P" := (big_opM bi_sep (λ _ x, P) m) : bi_scope.

Notation "'[∗' 'set]' x ∈ X , P" := (big_opS bi_sep (λ x, P) X) (only parsing) : bi_scope.
Notation "'[**' 'set]' x ∈ X , P" := (big_opS bi_sep (λ x, P) X) : bi_scope.

Notation "'[∗' 'mset]' x ∈ X , P" := (big_opMS bi_sep (λ x, P) X) (only parsing) : bi_scope.
Notation "'[**' 'mset]' x ∈ X , P" := (big_opMS bi_sep (λ x, P) X) : bi_scope.

(** Big conjunction *)

Notation "'[∧' 'list]' i ↦ x ∈ l , P" := (big_opL bi_and (λ i x, P) l) (only parsing) : bi_scope.
Notation "'[/\' 'list]' i |-> x ∈ l , P" := (big_opL bi_and (λ i x, P) l) : bi_scope.

Notation "'[∧' 'list]' x ∈ l , P" := (big_opL bi_and (λ _ x, P) l) (only parsing) : bi_scope.
Notation "'[/\' 'list]' x ∈ l , P" := (big_opL bi_and (λ _ x, P) l) : bi_scope.

(** Big disjunction *)

Notation "'[∨' 'list]' i ↦ x ∈ l , P" := (big_opL bi_or (λ i x, P) l) (only parsing) : bi_scope.
Notation "'[\/' 'list]' i |-> x ∈ l , P" := (big_opL bi_or (λ i x, P) l) : bi_scope.

Notation "'[∨' 'list]' x ∈ l , P" := (big_opL bi_or (λ _ x, P) l) (only parsing) : bi_scope.
Notation "'[\/' 'list]' x ∈ l , P" := (big_opL bi_or (λ _ x, P) l) : bi_scope.
