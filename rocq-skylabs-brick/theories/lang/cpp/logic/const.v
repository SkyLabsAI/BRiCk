(*
 * Copyright (c) 2022-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import iris.proofmode.monpred.

Require Import skylabs.prelude.base.

Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.logic.pred.
Require Import skylabs.lang.cpp.logic.path_pred.
Require Import skylabs.lang.cpp.logic.wp.
Require Import skylabs.lang.cpp.logic.heap_pred.
Require Import skylabs.prelude.telescopes.
Require Import skylabs.upoly.base.

#[local] Set Printing Coercions.

Section defs.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (ty : decltype) (Q : mpred).

  Import UPoly.

  (*
  [wp_const tu from to addr ty Q] replaces the [from] ownership of
  [ty] at [addr] with [to] ownership and then proceeds as [Q].

  This is used to implement [wp_make_const] and [wp_make_mutable].

  TODO: Consider adjusting the [wp_const] theory to use [sub_module]
  rather than [type_table_le] both for consistency and to benefit from
  the [RewriteRelation] instance.

  TODO: Consider reordering arguments to [wp_const] in order to bump
  [Params], ease the statement of [Proper] instances, and speed up
  setoid rewriting.
   *)
  Parameter wp_const : forall (tu : translation_unit) {σ : genv} (from to : cQp.t) (addr : ptr) (ty : decltype), Mglobal.M unit.

  (*
  Axiom wp_const_frame : forall tu tu' f t a ty Q Q',
    type_table_le tu.(types) tu'.(types) ->
    Q -* Q' |-- wp_const tu f t a ty Q -* wp_const tu' f t a ty Q'.

  Axiom wp_const_shift : forall tu f t a ty Q,
    (|={top}=> wp_const tu f t a ty (|={top}=> Q))
    |-- wp_const tu f t a ty Q.
   *)


  (*
  (* Naviely, this construction would probably provide fancy updates and laters *)
  Definition Mconsume_produce {TT1 TT2 : tele} (P : TT1 -t> mpred) (Q : TT1 -t> TT2 -t> mpred)
    : Mglobal.M (tele_append TT1 (tele_bind (fun _ => TT2))).
  Proof. Admitted.

  Notation eta F := (fun x => F x).
  #[universes(polymorphic)] Instance eta_M_MRet : MRet (eta M). Admitted.
  #[universes(polymorphic)] Instance eta_M_FMap : FMap (eta M). Admitted.
  #[universes(polymorphic)] Instance eta_M_Ap : Ap (eta M). Admitted.
  #[universes(polymorphic)] Instance eta_M_MBind : MBind (eta M). Admitted.
  *)

  Instance list_traverse : Traverse (eta list) :=
    fun F _ _ _ _ _ f => fix recurse ls :=
      match ls with
      | nil => mret nil
      | l :: ls => cons <$> f l <*> recurse ls
      end.

  (*
  TODO this needs to be extended because if it is casting <<volatile>>,
  then it needs to descend under <<const>>
  *)
  #[local] Notation "|={ E }=> P" := (|={E}=> P)%I (only parsing).
  #[local] Definition wp_const_body (wp_const : cQp.t -> cQp.t -> ptr -> decltype -> Mglobal.M unit)
      (tu : translation_unit) (from to : cQp.t)  (addr : ptr) (ty : decltype) : Mglobal.M unit :=
    let '(cv, rty) := decompose_type ty in
(*    let Q := |={top}=> Q in *)
    if q_const cv then mret ()
    else
      let UNSUPPORTED : Mglobal.M unit := wp_const from to addr ty in
      match rty return Mglobal.M unit with
      | Tptr _
      | Tnum _ _
      | Tchar_ _
      | Tbool
      | Tnullptr
      | Tenum _
      | Tmember_pointer _ _
      | Tfloat_ _
      | Tvoid =>
        let rty := erase_qualifiers rty in
        letWP* _ :=
          update (TT1:=[tele (_ : val)]) (TT2:=[tele])
            (fun v : val => addr |-> tptstoR rty from v)
            (fun v : val => addr |-> tptstoR rty to v)
        in mret ()

      | Tref rty
      | Trv_ref rty =>
        let rty := erase_qualifiers rty in
        letWP* _ :=
          update (TT1:=[tele (_ : val)]) (TT2:=[tele])
                          (fun v => addr |-> primR (Tref rty) from v)
                          (fun v => (addr |-> primR (Tref rty) to v))
        in mret ()
        (* ^ References must be initialized *)

      | Tarray ety sz =>
          letWP* _ :=
            traverse (fun i => wp_const from to (addr .[ erase_qualifiers ety ! Z.of_N i ]) ety)
                    (seqN 0 sz)
            in mret ()
      | Tincomplete_array _ =>
          Merror ("wp_const", ty)
      | Tvariable_array _ _ =>
          Merror ("wp_const", ty)

      | Tnamed cls =>
          match tu.(types) !! cls with
          | Some gd =>
              match gd with
              | Gunion u =>
                letWP* '(TeleArgCons br _) :=
                  update (TT1:=[tele (_ : option _)]) (TT2:=[tele])
                                   (fun br => addr |-> unionR cls from br)
                                   (fun br => addr |-> unionR cls to br)
                in
                match br with
                | None => mret ()
                | Some br => match u.(u_fields) !! br with
                            | None => contra (* unreachable *)
                            | Some m =>
                                if m.(mem_mutable)
                                then mret ()
                                else
                                  wp_const from to (addr ,, _field (Field cls m.(mem_name))) m.(mem_type)
                            end
                end
              | Gstruct st =>
                  letWP* _ := traverse (T:=eta list) (fun '(b, _) => wp_const from to (addr ,, _base cls b) (Tnamed b)) (s_bases st) in
                  letWP* _ := traverse (T:=eta list) (fun m =>
                                          if m.(mem_mutable)
                                          then mret ()
                                          else wp_const from to (addr ,, _field (Field cls m.(mem_name))) m.(mem_type))
                                       (s_fields st)
                  in
                  if has_vtable st then
                    (fun _ => ()) <$> update (TT1:=[tele (_ : _)]) (TT2:=[tele])
                      (fun path => addr |-> structR cls from ** addr |-> derivationR cls path from)
                      (fun path => addr |-> structR cls to ** addr |-> derivationR cls path to)
                  else
                    (fun _ => ()) <$> update (TT1:=[tele]) (TT2:=[tele])
                      (addr |-> structR cls from)
                      (addr |-> structR cls to)
              | Gtype
              | Genum _ _
              | Gconstant _ _
              | Gtypedef _
              | Gunsupported _ => UNSUPPORTED
              end
          | None => Munsupported ("wp_const", rty)
          end
      | Tfunction _
      | Tarch _ _ => Munsupported ("wp_const", rty)
      | Tqualified cv ty' => Merror ("wp_const", rty) (* unreachable *)
      | Tunsupported _ => Munsupported ("wp_const", rty)
      | Tparam _ | Tresult_param _
      | Tresult_global _
      | Tresult_unop _ _
      | Tresult_binop _ _ _
      | Tresult_call _ _
      | Tresult_member_call _ _ _
      | Tresult_member _ _
      | Tdecltype _
      | Texprtype _
      | Tauto
      | Tresult_parenlist _ _ => Munsupported ("wp_const", rty)
      end%I.

  (* NOTE: we prefer an entailment ([|--]) to a bi-entailment ([-|-]) or an equality
     to be conservative.
   *)
  Axiom wp_const_intro : forall tu f t a ty,
    Reduce (wp_const_body (wp_const tu) tu f t a ty)
    ⊆ wp_const tu f t a ty.

  (*
  Lemma wp_const_value_type_intro tu from to (p : ptr) ty Q :
    is_value_type ty ->
    (
      if qual_norm (fun cv _ => q_const cv) ty then Q
      else
        Exists v,
        let R q := p |-> tptstoR (erase_qualifiers ty) q v in
        R from ** (R to -* Q)
    )
    |-- wp_const tu from to p ty Q.
  Proof.
    rewrite is_value_type_decompose_type qual_norm_decompose_type.
    rewrite erase_qualifiers_decompose_type.
    have := is_qualified_decompose_type ty.
    rewrite -wp_const_intro.
    destruct (decompose_type ty) as [cv rty]; cbn=>??.
    case_match; first by rewrite -fupd_intro. destruct rty; try done.
    all: by iIntros "(% & R & HQ) !>"; iExists _; iFrame "R";
      iIntros "R !>"; iApply ("HQ" with "R").
  Qed.

  Lemma primR_wp_const_val tu from to (p : ptr) ty Q :
    is_value_type ty ->
    (
      if qual_norm (fun cv _ => q_const cv) ty
      then Q
      else
        Exists v,
        let R q := p |-> primR (erase_qualifiers ty) q v in
        R from ** (R to -* Q)
    )
    |-- wp_const tu from to p ty Q.
  Proof.
    intros. rewrite -wp_const_value_type_intro//.
    case_match; first done. iIntros "(%v & R & HQ)".
    iDestruct (primR_tptsto_acc with "R") as "(%v' & V & R & HR)".
    iExists v'. rewrite !_at_tptstoR. iFrame "R". iIntros "R".
    iApply "HQ". iApply ("HR" with "V R").
  Qed.

  Lemma primR_wp_const_ref tu from to (p : ptr) ty Q :
    is_reference_type ty ->
    (
      if qual_norm (fun cv _ => q_const cv) ty then Q
      else
        Exists v,
        let R q := p |-> primR (Tref $ erase_qualifiers $ as_ref ty) q v in
        R from ** (R to -* Q)
    )
    |-- wp_const tu from to p ty Q.
  Proof.
    cbn. rewrite is_reference_type_decompose_type.
    rewrite qual_norm_decompose_type as_ref_decompose_type.
    have := is_qualified_decompose_type ty.
    rewrite -wp_const_intro.
    destruct (decompose_type ty) as [cv rty]; cbn=>??.
    case_match; first by rewrite -fupd_intro. destruct rty; first [done | cbn].
    all: iIntros "(% & R & HQ) !>"; iExists _; iFrame "R";
      iIntros "R !>"; iApply ("HQ" with "R").
  Qed.

  (* Sanity check the [_frame] property *)
  Lemma fold_left_frame : forall B (l : list B) (f f' : mpred -> B -> mpred) (Q Q' : mpred),
    (Q -* Q') |-- □ (Forall Q1 Q1' a, (Q1 -* Q1') -* (f Q1 a -* f' Q1' a)) -*  fold_left f l Q -* fold_left f' l Q'.
  Proof.
    move=>B l.
    induction l; iIntros (????) "W #F"; first done.
    iDestruct ("F" $! Q Q' a with "W") as "W".
    iApply (IHl with "W"). eauto.
  Qed.

  (* Sanity check *)
  Lemma wp_const_body_frame CAST tu q q' p ty Q Q' :
    Q -* Q'
    |-- □ (Forall a b p ty Q Q', (Q -* Q') -* CAST a b p ty Q -* CAST a b p ty Q') -*
        wp_const_body CAST tu q q' p ty Q -* wp_const_body CAST tu q q' p ty Q'.
  Proof.
    rewrite /wp_const_body/=; intros.
    destruct (decompose_type ty) as [cv t].
    iIntros "F #C".
    case_match; first by iIntros ">X"; iApply "F".
    destruct t.

    (* unreachable *)
    all:try by
      lazymatch goal with
      | |- context [ False%I ] => by iIntros ">X"; iExFalso
      end.

    (* unsupported *)
    #[local] Ltac solve_unsupported :=
      by iIntros ">X"; iApply ("C" with "[F] X"); iIntros ">X"; iApply "F".
    all: try solve_unsupported.

    (* primitives *)
    all: try by iIntros ">[X | X]";
      [ iLeft; iDestruct "X" as (v) "[? X]"; iExists v; iFrame; iIntros "!> ?"; iApply "F"; iApply "X";  iFrame
      | iRight; iDestruct "X" as "[$ X]"; iIntros "!> ?"; iApply "F"; iApply "X"; iFrame ].

    (* references *)
    all: try by iIntros ">(%v & [? X])"; iExists v; iFrame; iIntros "!> ?"; iApply "F"; iApply "X"; iFrame.

    { (* arrays *)
      iIntros ">X !>". iRevert "X". iApply (fold_left_frame with "[F]").
      - iIntros ">X". by iApply "F".
      - iIntros "!>" (???) "F". by iApply "C".
    }

    { (* aggregates *)
      case_match; last solve_unsupported.
      case_match; try solve_unsupported.
      { (* unions *)
        iIntros ">X". iDestruct "X" as (?) "X".
        iExists _; iDestruct "X" as "[$ X]".
        iIntros "!> Y"; iSpecialize ("X" with "Y").
        case_match; last by iApply "F".
        case_match; last by iApply ("C" with "[F] X"); iIntros ">?"; by iApply "F".
        case_match; first by iApply "F".
        iApply ("C" with "[F] X"). iIntros ">?". by iApply "F". }
      { (* structs *)
        iIntros ">X !>". iRevert "X".
        iApply (fold_left_frame with "[F]").
        { iApply (fold_left_frame with "[F]").
          { case_match; iIntros "[$ X] Y".
            { iDestruct ("X" with "Y") as (path) "X"; iExists path; iDestruct "X" as "[$ X]"; iIntros "Y"; iApply "F".
              iApply "X"; eauto. }
            { iApply "F". iApply "X"; eauto. } }
          { iModIntro.
            iIntros (???) "F". case_match; eauto.
            iApply "C"; eauto. } }
        { iModIntro.
          iIntros (???) "F". case_match; eauto.
          iApply "C"; eauto. } } }
  Qed.

  (*
  Lemma cv_cast_body_frame : forall CAST CAST' tu tu' q q' p ty (Q Q' : mpred),
    sub_module tu tu' ->
        Q -* Q'
    |-- □ (Forall a b p ty Q Q', (Q -* Q') -* CAST a b p ty Q -* CAST' a b p ty Q') -*
        cv_cast_body CAST tu q q' p ty Q -* cv_cast_body CAST' tu' q q' p ty Q'.
  Proof.
    rewrite /cv_cast_body/=; intros.
    destruct (decompose_type ty) as [cv t].
    case_match.
    { iIntros "$ _"; eauto. }
    destruct t; eauto.

    (* unsupported *)
    all: try by iIntros "X C"; iApply "C"; eauto.

    (* primitives *)
    all: try solve [ iIntros "F #C X"; iDestruct "X" as "[X | X]";
        [ iLeft; iDestruct "X" as (v) "[? X]"; iExists v; iFrame; iIntros "?"; iApply "F"; iApply "X"; eauto
        | iRight; iDestruct "X" as "[$ X]"; iIntros "Y"; iApply "F"; iApply "X"; eauto ] ].

    (* references *)
    all: try solve [ iIntros "F #C X";
                     iDestruct "X" as (v) "[? X]"; iExists v; iFrame; iIntros "?"; iApply "F"; iApply "X"; eauto ].

    { (* arrays *)
      iIntros "F #C"; iApply (fold_left_frame with "F"); iModIntro. iIntros (???) "F"; iApply "C"; eauto.
    }

    { (* aggregates *)
      case_match; last first.
      { (* this case does not work out because i would need to go back to CAST' *)

      }
      case_match; last by iIntros "X C"; iApply "C"; eauto.
      case_match; try by iIntros "X C"; iApply "C"; eauto.
      { (* unions *)
        iIntros "F #C X"; iDestruct "X" as (?) "X".
        iExists _; iDestruct "X" as "[$ X]".
        iIntros "Y"; iSpecialize ("X" with "Y").
        case_match; last by iApply "F".
        case_match; eauto.
        case_match; first by iApply "F".
        iRevert "X"; iApply "C"; eauto. }
      { (* struct *)
        iIntros "F #C".
        iApply (fold_left_frame with "[F]").
        { iApply (fold_left_frame with "[F]").
          { iIntros "[$ X] Y"; iApply "F"; iApply "X"; eauto. }
          { iModIntro.
            iIntros (???) "F". case_match; eauto.
            iApply "C"; eauto. } }
        { iModIntro.
          iIntros (???) "F". case_match; eauto.
          iApply "C"; eauto. } } }
  Qed.
  *) *)

End defs.

Notation wp_make_const tu := (wp_const tu 1$m 1$c).
Notation wp_make_mutable tu := (wp_const tu 1$c 1$m).
