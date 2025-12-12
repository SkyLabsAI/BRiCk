(*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(**
 * reflecting virtual function dispatch in the logic.
 *)
Require Import bluerock.iris.extra.proofmode.proofmode.
Require Import bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.semantics.
Require Import bluerock.lang.cpp.logic.pred.
Require Import bluerock.lang.cpp.logic.heap_pred.
Require Import bluerock.lang.cpp.logic.path_pred.
Require Import bluerock.lang.cpp.logic.translation_unit.

Section with_cpp.
  Context `{Σ : cpp_logic}.

  (* [path_names ls] extracts the names from [ls], failing if any element is not
     [Tnamed n] for some [n]

     NOTE: this is effectively [traverse].
   *)
  Fixpoint path_names (ls : list type) : option (list globname) :=
    match ls with
    | nil => Some nil
    | Tnamed nm :: ls => cons nm <$> path_names ls
    | _ => None
    end.


  (** [base_to_derived derived path] is the offset to [derived]
      from the path [path]. For example,
      [[
      Eval simpl in base_to_derived "D" ["B";"A";"X"]%bs.
      (* = o_id ,, o_derived σ "X" "A" ,, o_derived σ "A" "B" ,, o_derived σ "B" "D" *)
      ]]

      NOTE the arguments are the same as [derived_to_base] but the direction
           of the cast is swapped.
   *)
  Fixpoint base_to_derived {σ : genv} (derived : globname) (path : list globname) : offset :=
    match path with
    | nil => o_id
    | base :: rest => o_dot (base_to_derived base rest) (o_derived σ base derived)
    end.

  Definition base_to_derived_ty {σ : genv} (derived : globname) (path : list type) : option offset :=
    base_to_derived derived <$> path_names path.

  Example _0 : forall {σ: genv},
      base_to_derived_ty "D" [Tnamed "C";Tnamed "B";Tnamed "A"] =
      Some (o_id ,, _derived "A" "B" ,, _derived "B" "C" ,, _derived "C" "D").
  Proof. reflexivity. Succeed Qed. Abort.

  (** [derived_to_base derived path] is the offset from [derived]
      from the path [path]. For example,
      [[
      Eval simpl in derived_to_base "::D" ["::B";"::A";"::X"]%bs.
      (* =  o_base σ "::D" "::B" ,, (o_base σ "::B" "::A" ,, (o_base σ "::A" "::X" ,, o_id)) *)
      ]]

      NOTE the arguments are the same as [base_to_derived] but the direction
           of the cast is swapped.
   *)
  Fixpoint derived_to_base {σ : genv} (derived : globname) (path : list globname) : offset :=
    match path with
    | nil => o_id
    | base :: rest => o_dot (o_base σ derived base) (derived_to_base base rest)
    end.

  Definition derived_to_base_ty {σ : genv} (derived : globname) (path : list type) : option offset :=
    derived_to_base derived <$> path_names path.

  Example _0 : forall {σ: genv},
      derived_to_base_ty "D" [Tnamed "C";Tnamed "B";Tnamed "A"] =
      Some (_base "D" "C" ,, (_base "C" "B" ,, (_base "B" "A" ,, o_id))).
  Proof. simpl. reflexivity. Succeed Qed. Abort.

  (** If successful, returns a pair of the function pointer to the
   *  implementation and the downcast for [this] pointer. *)
  Definition get_impl {σ} (base : globname) (path : list globname) (f : obj_name)
    : option (ptr * globname * offset) :=
    match dispatch.dispatch σ base path f with
    | None => None
    | Some (cls, path, fptr) => Some (_global fptr, cls, base_to_derived cls path)
    end.

  Section tu.
    Context `{σ : genv}.
    Variable tu : translation_unit.

    Definition tu_get_impl (base : globname) (path : list globname) (f : obj_name)
      : option (ptr * globname * offset) :=
      match dispatch.tu_dispatch tu base path f with
      | Some (cls, path, fptr) => Some (_global fptr, cls, base_to_derived cls path)
      | None => None
      end.

    Lemma tu_get_impl_ok (MOD : tu ⊧ σ) : forall base path fn a b c,
        tu_get_impl base path fn = Some (a, b, c) ->
        get_impl base path fn = Some (a, b, c).
    Proof.
      rewrite /tu_get_impl/get_impl; intros.
      do 3 (case_match; try congruence).
      erewrite tu_dispatch_ok; eauto.
    Qed.

    Lemma resolve_match_get_impl (MOD : tu ⊧ σ) {PROP : bi} base path fn a b c (P : _ -> PROP) :
        tu_get_impl base path fn = Some (a, b, c) ->
        P (a, b, c) -|-
      match get_impl base path fn with
      | Some x => P x
      | None => False
      end.
    Proof. intros; erewrite tu_get_impl_ok; eauto. Qed.
  End tu.

  (** [resolve_virtual σ this cls f Q] returns [Q fa this'] if resolving [f] on
      [this] results in a function that is equivalent to calling the pointer [fa]
      passing [this'] as the "this" argument.

      TODO: this definition should be changed to use [tu_get_impl] above.
   *)
  Definition resolve_virtual
             {σ : genv} (this : ptr) (cls : globname) (f : obj_name)
             (Q : forall (faddr : ptr) (cls_type : globname) (this_addr : ptr), mpred)
    : mpred :=
    Exists (path : list globname), (* denoteModule (resolve:=σ) tu ** *)
      ((Exists q, this |-> derivationR cls path q ** [| path <> nil |] ** True) //\\
      match get_impl cls path f with
      | Some (fa, cls, off) => Q fa cls (_offset_ptr this off)
      | None => (* the function was not found or the implementation was pure virtual *)
        False
      end).

  Lemma resolve_virtual_frame {σ : genv} (cls : globname) (this : ptr) f
    (Q Q' : ptr → globname → ptr → mpredI) :
        Forall (a : ptr) (b : globname) (c : ptr), Q a b c -* Q' a b c
    |-- resolve_virtual this cls f Q -* resolve_virtual this cls f Q'.
  Proof.
    intros.
    rewrite /resolve_virtual.
    iIntros "X Y".
    iDestruct "Y" as (path) "Y".
    iExists path; iFrame.
    iSplit.
    { iDestruct "Y" as "[$ _]". }
    { iDestruct "Y" as "[_ Y]". case_match => //.
      destruct p as [[??]?]. by iApply "X". }
  Qed.

End with_cpp.
