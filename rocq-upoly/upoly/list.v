(*
 * Copyright (C) 2023-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.upoly.prelude.
Require Import skylabs.upoly.base.
Require Import skylabs.upoly.UTypes.
Import UPoly.

(** * Lists *)
(**
This module is not meant to be <<Import>>ed.
*)

Declare Scope ulist_scope.
Delimit Scope ulist_scope with ulist.
#[global] Bind Scope ulist_scope with list.

#[local] Open Scope ulist_scope.

Definition foldl@{uA uB | } {A : Type@{uA}} {B : Type@{uB}} (f : B -> A -> A) :=
  fix foldl (acc : A) (l : list B) : A :=
  match l with
  | nil => acc
  | cons y l => foldl (f y acc) l
  end.

Definition foldr@{uA uB | } {A : Type@{uA}} {B : Type@{uB}} (f : B -> A -> A) (acc : A) :=
  fix foldr (l : list B) : A :=
  match l with
  | nil => acc
  | cons y l => f y (foldr l)
  end.

Definition rev_app {A} := fix rev_app (l : list A) : list A -> list A :=
  match l with
  | nil => fun k => k
  | cons x l => fun k => rev_app l (cons x k)
  end.
Definition rev {A} (l : list A) : list A := rev_app l nil.

Definition app' {A} (l k : list A) : list A := rev_app (rev l) k.

Definition app {A} := fix app (l : list A) : list A -> list A :=
  match l with
  | nil => fun k => k
  | cons x l => fun k => cons x (app l k)
  end.

Module Export Notations.
  Infix "::" := cons : ulist_scope.
  Notation "[ ]" := nil : ulist_scope.
  Notation "[ x ]" := (cons x nil) : ulist_scope.
  Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : ulist_scope.
  Infix "++" := app : ulist_scope.
End Notations.

Definition run {A} : list A -> Datatypes.list A :=
  foldr Datatypes.cons Datatypes.nil.
#[global] Arguments run _ & _ : assert.

Definition inj {A} : Datatypes.list A -> list A :=
  fold_right cons nil.
#[global] Arguments inj _ & _ : assert.

#[global] Instance map : FMap list := fun _ _ f => fix map l :=
  match l with
  | nil => nil
  | cons x l => cons (f x) (map l)
  end.
#[global] Arguments map {_ _} _ & _%_ulist : assert.

#[global] Instance ret : MRet list := fun _ x => [x].
#[global] Arguments ret {_} & _ : assert.

#[global] Instance bind : MBind list := fun A B (f : A -> list B) =>
  foldr (fun x ys => f x ++ ys) nil.
#[global] Arguments bind {_ _} _ & _%_ulist : assert.

#[global] Instance join : MJoin list := fun A =>
  foldr app nil.
#[global] Arguments join {_} & _%_ulist : assert.

Definition ap : Ap list := _.
#[global] Arguments ap {_ _} & (_ _)%_ulist : assert.

#[global] Instance traverse : Traverse list := fun F _ _ _ A B (f : A -> F B) =>
  foldr (fun x acc => cons <$> f x <*> acc) (mret []).
#[global] Arguments traverse {_ _ _ _ _ _} & _ _%_ulist : assert.

#[global] Instance fail : MFail list := fun _ _ => nil.
#[global] Arguments fail {_} _ : assert.

#[global] Instance catch : MCatch unit list := fun _ l h =>
  if l is nil then h () else l.
#[global] Arguments catch {_} & _%_ulist _ : assert.

Definition alternative : Alternative list := _.
#[global] Arguments alternative {_} & _%_ulist _ : assert.

#[global] Instance lift_list : MLift (eta Datatypes.list) list := fun A l =>
  List.fold_left (fun xs x => x :: xs) l nil.
#[global] Instance lift_optionp : MLift UTypes.option list := fun A m =>
  if m is Some x then [x] else nil.
#[global] Instance lift_option : MLift (eta Datatypes.option) list := fun A m =>
  if m is Datatypes.Some x then [x] else nil.

#[global] Instance lookup A : Lookup nat A (list A) :=
  fix lookup n l :=
  match l with
  | nil => Datatypes.None
  | cons x l =>
    match n with
    | O => Datatypes.Some x
    | S n => lookup n l
    end
  end.
#[global] Arguments lookup {_} & _ _%_ulist : assert.

Definition length {A} := fix length (l : list A) : nat :=
  match l with
  | nil => 0
  | cons x l => S (length l)
  end.

Definition take {A} := fix take (n : nat) (l : list A) {struct n} : list A :=
  match n , l with
  | S n , cons x l => cons x (take n l)
  | _ , _ => nil
  end.

Definition drop {A} := fix drop (n : nat) (l : list A) {struct n} : list A :=
  match n , l with
  | S n , cons x l => drop n l
  | _ , _ => l
  end.

Definition nth_def {A} (def : A) := fix nth_def (n : nat) (l : list A) {struct n} : A :=
  match n , l with
  | _ , nil => def
  | O , cons x _ => x
  | S n , cons _ l => nth_def n l
  end.

Definition force_list_dep {A} :=
  fix force_list_dep {P : list A -> Type} (l : list A) (p : ∀ l, P l) : P l :=
  match l with
  | nil => p nil
  | cons x l => force_list_dep l (fun l => p (cons x l))
  end.
Definition force_list {A P} (l : list A) (p : list A -> P) : P := force_list_dep l p.

Definition force_app_dep {A} := fix force_app_dep {P : list A -> Type} (l : list A)
    : ∀ (k : list A) (p : ∀ l, P l), P (app l k) :=
  match l with
  | nil => fun k p => p k
  | cons x l => fun k p => force_app_dep l k (fun l => p (cons x l))
  end.
Definition force_app {A P} (l k : list A) (p : list A -> P) : P := force_app_dep l k p.

Definition force_map {A B K} :=
  fix force_map (l : list A) (f : ∀ K' (k : B -> K'), A -> K') (k : list B -> K) : K :=
  match l with
  | nil => k nil
  | cons x l => f _ (fun y => force_map l f (fun l => k (cons y l))) x
  end.

Definition map_filter {A B} (f : A -> option B) :=
  fix map_filter (l : list A) : list B :=
  match l with
  | nil => nil
  | cons x l =>
    match f x with
    | Some y => cons y (map_filter l)
    | None => map_filter l
    end
  end.

Definition zip_with {A B C} (f : A -> B -> C) :=
  fix zip_with (l : list A) (k : list B) : list C :=
  match l with
  | nil => nil
  | cons x l =>
    match k with
    | nil => nil
    | cons y k => cons (f x y) (zip_with l k)
    end
  end.

Definition select {A} (mask : list bool) (l : list A) : list A :=
  map_filter (fun '(pair b x) => if b is true then Some x else None)
    (zip_with pair mask l).

Section list.
  Context {A : Type}.
  Implicit Types (l : list A).

  Lemma map_id l : map id l = l.
  Proof. induction l; by rewrite //= IHl. Qed.

  Lemma length_map {B} (f : A -> B) l : length (map f l) = length l.
  Proof. induction l; [|cbn; rewrite IHl]; reflexivity. Qed.

  Lemma map_app {B} (f : A -> B) l k : map f (l ++ k) = map f l ++ map f k.
  Proof. induction l; simpl; [reflexivity | ]. rewrite IHl. reflexivity. Qed.

  Lemma take_drop n l : app (take n l) (drop n l) = l.
  Proof.
    revert l; induction n; [reflexivity|]; intros l.
    destruct l; simpl; [reflexivity|].
    rewrite IHn. reflexivity.
  Qed.

  Lemma force_list_dep_correct {P : list A -> Type} (p : ∀ l, P l) l :
    force_list_dep l p = p l.
  Proof.
    revert P p; induction l; intros P p.
    - reflexivity.
    - cbn. rewrite IHl. reflexivity.
  Qed.

  Lemma force_list_correct {P : Type} l (p : list A -> P) :
    force_list l p = p l.
  Proof. unfold force_list. refine (force_list_dep_correct _ _). Qed.

  Lemma force_app_dep_correct {P : list A -> Type} (p : ∀ l, P l) l k :
    force_app_dep l k p = p (l ++ k).
  Proof.
    revert P p k; induction l; intros P p k.
    - reflexivity.
    - cbn. rewrite IHl. reflexivity.
  Qed.

  Lemma force_app_correct {P : Type} l k (p : list A -> P) :
    force_app l k p = p (l ++ k).
  Proof. unfold force_list. refine (force_app_dep_correct _ _ _). Qed.

  Lemma force_map_ok {B} l (f : _) (k : list B -> Prop) :
    (∀ x, ∃ y, ∀ K' g, f K' g x = g y) ->
    k (map (fun x => f B (fun y => y) x) l) ->
    force_map l f k.
  Proof.
    intros Hf.
    revert k; induction l; intros k; [intros H; exact H|].
    cbn. intros.
    edestruct Hf as [y Hf']; rewrite -> Hf'.
    apply IHl. revert H. rewrite Hf'.
    intros H; exact H.
  Qed.
  Lemma force_map_ko {B} (l : list A) (f : _) (k : list B → Prop) :
    (∀ x, ∃ y, ∀ K' g, f K' g x = g y) ->
    force_map l f k ->
    k (map (λ x, f B (λ y, y) x) l).
  Proof.
    intros Hf.
    revert k; induction l; intros k; [intros H; exact H|].
    cbn. intros.
    edestruct Hf as [y Hf']; rewrite -> Hf'.
    apply IHl. revert H. rewrite Hf'.
    intros H; exact H.
  Qed.
End list.
