(*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** this module provides a denotational/axiomatic semantics to c++ compilation
    units.
 *)
Require Import bluerock.prelude.base.
Require Import bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.semantics.
Require Import bluerock.lang.cpp.logic.pred.
Require Import bluerock.lang.cpp.logic.path_pred.
Require Import bluerock.lang.cpp.logic.heap_pred.
Require Import bluerock.iris.extra.proofmode.proofmode.

Import ChargeNotation.


Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  Definition init_validR (ty : type) : Rep :=
    if zero_sized_array ty then
      validR
    else
      svalidR.
  #[global] Hint Opaque init_validR : br_opacity.
  #[global] Instance init_validR_persistent : Persistent1 init_validR.
  Proof. intros; rewrite /init_validR; case_match; apply _. Qed.
  #[global] Instance init_validR_affine : Affine1 init_validR := _.

  Definition denoteSymbol (tu : translation_unit) (n : obj_name) (o : ObjValue) : mpred :=
    _global n |->
        match o with
        | Ovar t e => init_validR t
        | Ofunction f =>
          match f.(f_body) with
          | None => svalidR
          | Some body => as_Rep (code_at tu f)
          end
        | Omethod m =>
          match m.(m_body) with
          | None => svalidR
          | Some body => as_Rep (method_at tu m)
          end
        | Oconstructor c =>
          match c.(c_body) with
          | None => svalidR
          | Some body => as_Rep (ctor_at tu c)
          end
        | Odestructor d =>
          match d.(d_body) with
          | None => svalidR
          | Some body => as_Rep (dtor_at tu d)
          end
        end.
  #[global] Hint Opaque denoteSymbol : br_opacity.

  #[global] Instance denoteSymbol_persistent {tu n o} : Persistent (denoteSymbol tu n o).
  Proof. rewrite /denoteSymbol; repeat case_match; apply _. Qed.

  #[global] Instance denoteSymbol_affine {tu n o} : Affine (denoteSymbol tu n o) := _.

  (** [is_strict_valid o] states that if the declaration [o] occurs in a
      translation unit, the pointer to it is guaranteed to be strictly valid.
   *)
  Definition is_strict_valid (o : ObjValue) : bool :=
    match o with
    | Ovar t _ => negb (zero_sized_array t)
    | _ => true
    end.

  Lemma denoteSymbol_strict_valid tu n o :
    is_strict_valid o ->
    denoteSymbol tu n o |-- strict_valid_ptr (_global n).
  Proof.
    rewrite /denoteSymbol/init_validR/is_strict_valid; destruct o.
    { rewrite -_at_svalidR. by destruct zero_sized_array. }
    all: intros _; case_match; last by rewrite _at_svalidR.
    all: rewrite !_at_as_Rep; auto using
      code_at_strict_valid, method_at_strict_valid, ctor_at_strict_valid, dtor_at_strict_valid.
  Qed.

  Lemma denoteSymbol_valid tu n o :
    denoteSymbol tu n o |-- valid_ptr (_global n).
  Proof.
    destruct (is_strict_valid o) eqn:Hs.
    { by rewrite denoteSymbol_strict_valid ?Hs // strict_valid_valid. }
    move: Hs.
    rewrite -_at_validR /denoteSymbol /init_validR /is_strict_valid.
    by destruct o => //= ?; case_match.
  Qed.

  (** TODO incomplete *)
  Definition initSymbol (n : obj_name) (o : ObjValue) : mpred :=
    _at (_global n)
        match o with
        | Ovar t (global_init.Init e) =>
          emp (*
      Exists Q : FreeTemps -> mpred,
      □ (_at (_eq a) (uninitR (resolve:=resolve) t 1) -*
         Forall ρ ti, wp_init (resolve:=resolve) ti ρ t (Vptr a) e Q) ** Q emp
*)
      (* ^^ todo(gmm): static initialization is not yet supported *)
        | Ovar t global_init.NoInit =>
          uninitR t 1$m
        | _ => emp
        end.

  Definition denoteModule_def (tu : translation_unit) : mpred :=
    ([∗list] sv ∈ map_to_list tu.(symbols), denoteSymbol tu sv.1 sv.2) **
    [| module_le tu σ.(genv_tu) |].
  Definition denoteModule_aux : seal (@denoteModule_def). Proof. by eexists. Qed.
  Definition denoteModule := denoteModule_aux.(unseal).
  Definition denoteModule_eq : @denoteModule = _ := denoteModule_aux.(seal_eq).

  #[global] Hint Opaque denoteModule : typeclass_instances.

  #[global] Instance denoteModule_persistent {module} : Persistent (denoteModule module).
  Proof.
    red. rewrite denoteModule_eq /denoteModule_def; intros.
    destruct module; simpl.
    iIntros "[#M #H]"; iFrame "#".
  Qed.

  #[global] Instance denoteModule_affine {module} : Affine (denoteModule module).
  Proof. refine _. Qed.

  Lemma denoteModule_denoteSymbol n m o :
    m.(symbols) !! n = Some o ->
    denoteModule m |-- denoteSymbol m n o.
  Proof.
    rewrite denoteModule_eq/denoteModule_def.
    iIntros (Hlookup) "[M _]".
    move: (NM.map_to_list_elements _ _ _ Hlookup) => [l1][l2] ->.
    rewrite big_opL_app big_opL_cons.
    by iDestruct "M" as "[_ [M _]]".
  Qed.

  Lemma denoteModule_strict_valid n m :
    is_strict_valid <$> (m.(symbols) !! n) = Some true ->
    denoteModule m |-- strict_valid_ptr (_global n).
  Proof.
    case E: lookup => [s |//] /= [Hs].
    by rewrite denoteModule_denoteSymbol // denoteSymbol_strict_valid // Hs.
  Qed.

  Lemma denoteModule_valid n m :
    m.(symbols) !! n <> None ->
    denoteModule m |-- valid_ptr (_global n).
  Proof.
    intros; iIntros "M".
    destruct (symbols m !! n) eqn:?; try congruence.
    iDestruct (denoteModule_denoteSymbol with "M") as "M"; eauto.
    by iApply denoteSymbol_valid.
  Qed.

  #[global] Instance denoteModule_models_observe tu : Observe [| tu ⊧ σ |] (denoteModule tu).
  Proof.
    apply observe_intro_only_provable.
    rewrite denoteModule_eq/denoteModule_def.
    iIntros "[_ %]". iPureIntro. constructor.
    destruct (module_le_spec tu (genv_tu σ)); eauto.
    destruct H.
  Qed.

End with_cpp.

Arguments denoteModule _ : simpl never.
