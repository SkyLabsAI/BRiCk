(*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import stdpp.fin_maps.
Require Export bluerock.prelude.base.
Require Import bluerock.prelude.avl.
Require Import bluerock.lang.cpp.syntax.

(** TODO rename [sub_module] since it is not actually about modules
    TODO use [⊆] as the "generic" name by declaring [SubsetEq] instances
         at each level.
 *)

(** * Sub-module

    [sub_module a b] states that the [translation_unit] [a] is included
    in the [translation_unit] [b].
 *)


(* Some tactics *)
#[local] Ltac do_bool_decide :=
  repeat match goal with
    | H : False |- _ => contradiction
    | H : Is_true _ |- _ => red in H
    | H : _ && _ = true |- _ => apply andb_true_iff in H; destruct H
    | H : bool_decide _ = false |- _ => apply bool_decide_eq_false_1 in H
    | H : bool_decide _ = true |- _ => apply bool_decide_eq_true_1 in H
    | |- _ && _ = true => apply andb_true_iff; split
    end.
#[local] Ltac smash :=
  intuition idtac; repeat (do_bool_decide; subst; repeat case_match);
  eauto using bool_decide_eq_true_2; try congruence.

(** * Definitions for decidability *)
Section compat_le.
  Context {T : Type}.
  Variable (f : option T -> option T -> bool).

  (* NOTE: this is effectively [Decision (map_inclusion)],
     but is significantly more computationally efficient *)
  Definition compat_le (l r : NM.t T) : bool :=
    negb $ NM.find_any (fun k v => negb (f (Some v) (r !! k))) l.

  Lemma compat_le_sound : forall l r,
      (forall x, f None x = true) ->
      if compat_le l r then
        forall k, f (l !! k) (r !! k) = true
      else
        exists k, f (l !! k) (r !! k) = false.
  Proof.
    intros.
    unfold compat_le.
    generalize (NM.find_any_ok (λ k (v : T), negb (f (Some v) (r !! k))) l).
    generalize (NM.find_any (λ k (v : T), negb (f (Some v) (r !! k))) l).
    destruct b; simpl; intros.
    - destruct H0 as [ ? [ ? [ ? ? ] ] ].
      exists x. unfold lookup in *.
      apply negb_true_iff in H1.
      erewrite NM.find_1; eauto.
    - unfold lookup, NM.map_lookup.
      destruct (NM.find k l) eqn:Heq; eauto.
      apply NM.find_2 in Heq.
      eapply H0 in Heq.
      apply negb_false_iff in Heq. eauto.
  Qed.

End compat_le.

(** ** Inclusion of types ([GlobDecl]) *)

(** [GlobDecl_le a b] holds when [a] has compatible (but possibly less)
    information than [b].
    For example, [a] might be a type declaration while [b] is a compatible
    definition. *)
Definition GlobDecl_le (a b : GlobDecl) : bool :=
  match a , b with
  | Gtype , Gtype
  | Gtype , Genum _ _
  | Gtype , Gunion _
  | Gtype , Gstruct _
  | Gtype , Gunsupported _ => true
  | Gunion _ , Gtype
  | Gstruct _ , Gtype => false
  | Gunion u , Gunion u' =>
    bool_decide (u = u')
  | Gstruct s , Gstruct s' =>
    bool_decide (s = s')
  | Genum e _ , Genum e' _ =>
    bool_decide (e = e')
  | Gconstant t (Some e) , Gconstant t' (Some e') =>
    bool_decide (t = t') && bool_decide (e = e')
  | Gconstant t (Some _) , Gconstant t' None => false
  | Gconstant t None , Gconstant t' (Some e') =>
    bool_decide (t = t')
  | Gconstant t None , Gconstant t' None =>
    bool_decide (t = t')
  | Gtypedef t , Gtypedef t' =>
    bool_decide (t = t')
  | Gunsupported m , Gunsupported m' => bool_decide (m = m')
  | _ , _ => false
  end.
Definition GlobDecl_ler := λ g1 g2, Is_true $ GlobDecl_le g1 g2.
Arguments GlobDecl_ler !_ _ /.

Section GlobDecl_ler.
  #[local] Notation GlobDecl_ler := (GlobDecl_ler).
  #[local] Instance GlobDecl_le_refl : Reflexive GlobDecl_ler.
  Proof.
    intros []; rewrite /= ?require_eq_refl; smash.
  Qed.

  #[local] Instance GlobDecl_le_trans : Transitive GlobDecl_ler.
  Proof.
    intros gd1 gd2 gd3; destruct gd1, gd2, gd3 => //=; smash.
  Qed.

  #[global] Instance: PreOrder GlobDecl_ler := {}.

  (* From this, it should follow that multiple translation units from the same
  [genv] must have compatible definitions. See [sub_modules_agree_globdecl] *)
  Lemma GlobDecl_ler_join gd1 gd2 gd3 :
    GlobDecl_ler gd1 gd3 -> GlobDecl_ler gd2 gd3 ->
    GlobDecl_ler gd1 gd2 \/ GlobDecl_ler gd2 gd1.
  Proof.
    destruct gd1, gd2 => //=; destruct gd3 => //=; smash.
    left; smash.
  Qed.
End GlobDecl_ler.


(**
   Compatibility of [GlobDecl] states that they contain consistent information.
   Since declarations can not be partially defined, it is sufficient to define
   this by saying that one subsumes the other.

   Note this relation is reflexive and symmetric, but *not* transitive.
 *)
Definition GlobDecl_compat gd1 gd2 :=
  GlobDecl_ler gd1 gd2 \/ GlobDecl_ler gd2 gd1.

#[local] Instance GlobDecl_compat_refl : Reflexive GlobDecl_compat.
Proof. left. reflexivity. Qed.

#[local] Instance GlobDecl_compat_sym : Symmetric GlobDecl_compat.
Proof. red. rewrite /GlobDecl_compat; destruct 1; tauto. Qed.

(** TODO: consolidate with other definitions *)
Lemma enum_compat {t1 t2 a b} :
  GlobDecl_compat (Genum t1 a) (Genum t2 b) ->
  t1 = t2.
Proof.
  rewrite /GlobDecl_compat/GlobDecl_ler/=.
  destruct 1.
  case_bool_decide; eauto; contradiction.
  case_bool_decide; eauto; contradiction.
Qed.


(** *** Inclusion of [type_table]s *)

Definition type_table_le (te1 te2 : type_table) : Prop :=
  forall gn gv,
    te1 !! gn = Some gv ->
    exists gv', te2 !! gn = Some gv' /\ GlobDecl_ler gv gv'.

(* TODO: consider replacing [type_table_le]'s definition with [type_table_le_alt] *)
Definition type_table_le_alt : type_table -> type_table -> Prop :=
  map_included (fun _ => GlobDecl_ler).
#[global] Instance: PreOrder type_table_le_alt.
Proof. apply @map_included_preorder, _. Qed.

Lemma type_table_le_equiv te1 te2 : type_table_le te1 te2 <-> type_table_le_alt te1 te2.
Proof.
  apply iff_forall => i; unfold option_relation.
  (* XXX TC inference produces different results here. Hacky fix. *)
  unfold type_table, globname, ident.
  repeat case_match; try naive_solver.
Qed.

#[global] Instance: PreOrder type_table_le.
Proof.
  eapply preorder_proper.
  apply: type_table_le_equiv.
  apply _.
Qed.

#[global,program]
Instance type_table_le_dec : RelDecision type_table_le :=
  fun a b =>
    match compat_le (fun l r => match l , r with
                             | None , _ => true
                             | Some _ , None => false
                             | Some l , Some r => GlobDecl_le l r
                             end) a b as X return _ = X -> _ with
    | true => fun pf => left _
    | false => fun pf => right _
    end eq_refl.
Next Obligation.
  intros.
  match goal with
  | _ : compat_le ?F _ _ = _ |- _ => generalize (@compat_le_sound _ F a b (fun _ => eq_refl))
  end; rewrite pf.
  rewrite /type_table_le.
  intros. specialize (H gn). rewrite H0 in H.
  case_match.
  - eexists; split; eauto. do 2 red. rewrite H. done.
  - congruence.
Qed.
Next Obligation.
  intros.
  match goal with
  | _ : compat_le ?F _ _ = _ |- _ => generalize (@compat_le_sound _ F a b (fun _ => eq_refl))
  end; rewrite pf.
  rewrite /type_table_le.
  intros. intro. destruct H.
  case_match; try congruence.
  destruct (H0 _ _ H1) as [ ? [ Heq ? ] ].
  rewrite Heq in H.
  do 2 red in H2. rewrite H in H2. assumption.
Qed.

(** ** Inclusion of [ObjValue] *)

(** [ObjVal_le a b] holds when [a] has compatible (but possibly less)
    information than [b].
    For example, [a] might be a declaration while [b] is a compatible
    definition.

    Note: We reduce [&&] so that it is lazy in its second argument.
 *)
Definition ObjValue_le (a b : ObjValue) : bool := Eval cbv beta iota zeta delta [ andb ] in
  let drop_norm t := drop_qualifiers $ normalize_type t in
  match a , b with
  | Ovar t oe , Ovar t' oe' =>
    bool_decide (t = t') &&
      match oe , oe' with
      | global_init.NoInit , global_init.NoInit => true
      | global_init.ImplicitInit , global_init.ImplicitInit => true
      | global_init.ImplicitInit , global_init.Init _ => true
      | global_init.Extern , _ => true
      | global_init.Delayed , global_init.Delayed => true
      | global_init.Init l , global_init.Init r => bool_decide (l = r)
      | _ , _ => false
      end
  | Ofunction f , Ofunction f' =>
    bool_decide (f.(f_cc) = f'.(f_cc)) &&
    bool_decide (f.(f_arity) = f'.(f_arity)) &&
    bool_decide (normalize_type f.(f_return) = normalize_type f'.(f_return)) &&
      match f.(f_body) , f'.(f_body) with
      | None , _ =>
        bool_decide (List.map (fun b => drop_norm b.2) f.(f_params) =
                     List.map (fun b => drop_norm b.2) f'.(f_params))
      | Some b , Some b' =>
        bool_decide (f.(f_params) = f'.(f_params)) &&
        bool_decide (b = b')
      | _ , None => false
      end
  | Omethod m , Omethod m' =>
    bool_decide (m.(m_cc) = m'.(m_cc)) &&
    bool_decide (m.(m_arity) = m'.(m_arity)) &&
    bool_decide (m.(m_class) = m'.(m_class)) &&
    bool_decide (m.(m_this_qual) = m'.(m_this_qual)) &&
    bool_decide (normalize_type m.(m_return) = normalize_type m'.(m_return)) &&
    match m.(m_body) , m'.(m_body) with
    | None , _ =>
      bool_decide (List.map (fun b => drop_norm b.2) m.(m_params) =
                   List.map (fun b => drop_norm b.2) m'.(m_params))
    | Some b , Some b' =>
      bool_decide (m.(m_params) = m'.(m_params)) &&
      bool_decide (b = b')
    | _ , None => false
    end
  | Oconstructor c , Oconstructor c' =>
    bool_decide (c.(c_cc) = c'.(c_cc)) &&
    bool_decide (c.(c_arity) = c'.(c_arity)) &&
    bool_decide (c.(c_class) = c'.(c_class)) &&
    match c.(c_body) , c'.(c_body) with
    | None , _ =>
      bool_decide (List.map (fun x => drop_norm x.2) c.(c_params) =
                   List.map (fun x => drop_norm x.2) c'.(c_params))
    | _ , None => false
    | Some x , Some y =>
      bool_decide (c.(c_params) = c'.(c_params)) &&
      bool_decide (x = y)
    end
  | Odestructor dd , Odestructor dd' =>
    bool_decide (dd.(d_cc) = dd'.(d_cc)) &&
    bool_decide (dd.(d_class) = dd'.(d_class)) &&
    match dd.(d_body) , dd'.(d_body) with
    | None , _ => true
    | _ , None => false
    | Some x , Some y => bool_decide (x = y)
    end
  | _ , _ => false
  end.
Definition ObjValue_ler : relation ObjValue := λ g1 g2, ObjValue_le g1 g2 = true. (* TODO use [Is_true] *)
Arguments ObjValue_ler !_ _ /.

Section ObjValue_ler.
  #[local] Instance ObjValue_le_refl : Reflexive ObjValue_ler.
  Proof.
    rewrite /ObjValue_ler/ObjValue_le => ?; smash.
  Qed.

  #[local] Instance ObjValue_le_trans : Transitive ObjValue_ler.
  Proof.
    intros a b c.
    destruct a, b => //=; (destruct c => //=; intros;
    repeat lazymatch goal with
           | H : Func' |- _ => destruct H; simpl in *
           | H : Method' |- _ => destruct H; simpl in *
           | H : Ctor' |- _ => destruct H; simpl in *
           | H : Dtor' |- _ => destruct H; simpl in *
           | H : false = true |- _ => inversion H
           | H : true = false |- _ => inversion H
           | H : bool_decide _ = true |- _ => apply bool_decide_eq_true_1 in H; subst
           | H : context [ if @bool_decide ?P ?DEC then _ else _ ] |- _ =>
                destruct (@bool_decide_reflect P DEC); subst
           | H : match ?X with _ => _ end = _ |- _ => destruct X eqn:?
           | |- bool_decide _ = _ => apply bool_decide_eq_true_2
           | |- context [ bool_decide ?X ] => rewrite (bool_decide_eq_true_2 X); [ | by etrans; eauto ]
           end; solve [ eauto | etrans; eauto ]).
  Qed.

  #[global] Instance: PreOrder ObjValue_ler := {}.
End ObjValue_ler.

(** *** Inclusion of [symbol_table]s *)
(* Ditto. *)
Definition sym_table_le_alt : symbol_table -> symbol_table -> Prop :=
  map_included (fun _ => ObjValue_ler).
#[global] Instance: PreOrder sym_table_le_alt.
Proof. apply @map_included_preorder, _. Qed.

Definition sym_table_le (a b : symbol_table) :=
  forall on v,
      a !! on = Some v ->
      exists v', b !! on = Some v' /\
            ObjValue_ler v v'.

Lemma sym_table_le_equiv te1 te2 : sym_table_le te1 te2 <-> sym_table_le_alt te1 te2.
Proof.
  apply iff_forall => i; unfold option_relation.
  (* XXX TC inference produces different results here. Hacky fix, as above. *)
  unfold symbol_table, globname, obj_name, ident.
  repeat case_match; naive_solver.
Qed.

#[global] Instance: PreOrder sym_table_le.
Proof.
  eapply preorder_proper.
  apply: sym_table_le_equiv.
  apply _.
Qed.

#[global,program]
Instance sym_table_le_dec a b : Decision (sym_table_le a b) :=
  match compat_le (fun l r => match l , r with
                           | None , _ => true
                           | Some _ , None => false
                           | Some l , Some r => ObjValue_le l r
                           end) a b as X return _ = X -> _ with
  | true => fun pf => left _
  | false => fun pf => right _
  end eq_refl.
Next Obligation.
  intros.
  match goal with
  | _ : compat_le ?F _ _ = _ |- _ => generalize (@compat_le_sound _ F a b (fun _ => eq_refl))
  end; rewrite pf.
  rewrite /sym_table_le.
  intros. specialize (H on). rewrite H0 in H.
  case_match.
  - eexists; split; eauto.
  - congruence.
Qed.
Next Obligation.
  intros.
  match goal with
  | _ : compat_le ?F _ _ = _ |- _ => generalize (@compat_le_sound _ F a b (fun _ => eq_refl))
  end; rewrite pf.
  rewrite /sym_table_le.
  intros. intro. destruct H.
  case_match; try congruence.
  destruct (H0 _ _ H1) as [ ? [ Heq ? ] ].
  rewrite Heq in H.
  red in H2. rewrite H in H2. congruence.
Qed.

(* TODO: complete_decl *)
#[local] Hint Constructors complete_decl complete_basic_type complete_type
  complete_pointee_type wellscoped_type wellscoped_types : core.

Lemma complete_decl_respects_GlobDecl_le {te g1 g2} :
  GlobDecl_ler g1 g2 ->
  complete_decl te g1 ->
  complete_decl te g2.
Proof.
  intros Hle Hct; inversion Hct; simplify_eq; destruct g2 => //=;
     simpl in *; do_bool_decide; subst; smash.
Qed.

#[local] Definition complete_decl_respects te2 g := ∀ te1,
  type_table_le te2 te1 ->
  complete_decl te1 g.
#[local] Definition complete_basic_type_respects te2 t := ∀ te1,
  type_table_le te2 te1 ->
  complete_basic_type te1 t.
#[local] Definition complete_pointee_type_respects te2 t := ∀ te1,
  type_table_le te2 te1 ->
  complete_pointee_type te1 t.
#[local] Definition complete_type_respects te2 t := ∀ te1,
  type_table_le te2 te1 ->
  complete_type te1 t.
#[local] Definition wellscoped_type_respects te2 ts := ∀ te1,
  type_table_le te2 te1 ->
  wellscoped_type te1 ts.
#[local] Definition wellscoped_types_respects te2 ts := ∀ te1,
  type_table_le te2 te1 ->
  wellscoped_types te1 ts.

(* Actual mutual induction. *)
Lemma complete_respects_sub_table_mut te2 :
  (∀ g : GlobDecl, complete_decl te2 g → complete_decl_respects te2 g) ∧
  (∀ t : type, complete_basic_type te2 t → complete_basic_type_respects te2 t) ∧
  (∀ t : type, complete_pointee_type te2 t → complete_pointee_type_respects te2 t) ∧
  (∀ t : type, complete_type te2 t → complete_type_respects te2 t) ∧
  (∀ t : type, wellscoped_type te2 t → wellscoped_type_respects te2 t) ∧
  (∀ t : list type, wellscoped_types te2 t → wellscoped_types_respects te2 t).
Proof.
  apply complete_mut_ind; try solve [intros; red; repeat_on_hyps (fun H => red in H); eauto]. {
    intros * Hlook ? Hsub.
    destruct (Hsub _ _ Hlook) as (st1 & Hlook1 & _).
    eapply (complete_pt_named _ Hlook1).
  }
  - intros * Hlook Hct IH ? Hsub.
    destruct (Hsub _ _ Hlook) as (st1 & Hlook1 & Hle).
    do 3 red in Hle. smash.
  - intros * Hlook Hct IH ? Hsub.
    destruct (Hsub _ _ Hlook) as (st1 & Hlook1 & Hle).
    apply (complete_named _ Hlook1).
    apply (complete_decl_respects_GlobDecl_le Hle), IH, Hsub.
Qed.

Lemma complete_type_respects_sub_table te1 te2 t :
  type_table_le te2 te1 ->
  complete_type te2 t → complete_type te1 t.
Proof. intros. by eapply complete_respects_sub_table_mut. Qed.

(** ** Inclusion on [translation_unit] *)

Record sub_module (a b : translation_unit) : Prop :=
{ types_compat : type_table_le a.(types) b.(types)
; syms_compat : sym_table_le a.(symbols) b.(symbols)
; byte_order_compat : a.(byte_order) = b.(byte_order) }.

Section sub_module.
  #[local] Instance: Reflexive sub_module.
  Proof. done. Qed.

  #[local] Instance: Transitive sub_module.
  Proof. intros ??? [] []; split; by etrans. Qed.

  #[global] Instance: PreOrder sub_module := {}.
End sub_module.
#[global] Instance: RewriteRelation sub_module := {}.

(** * Decidability

    [sub_module] is decidable
 *)
Definition module_le (a b : translation_unit) : bool :=
  Eval cbv beta iota zeta delta [ andb ] in
  bool_decide (a.(byte_order) = b.(byte_order)) &&
  bool_decide (type_table_le a.(types) b.(types)) &&
  bool_decide (sym_table_le a.(symbols) b.(symbols)).

Theorem module_le_sound : forall a b, if module_le a b then
                                   sub_module a b
                                 else
                                   ~sub_module a b.
Proof.
  rewrite /module_le; intros.
  repeat case_bool_decide.
  { constructor; eauto. }
  { intro C; inversion C; eauto. }
  { intro C; inversion C; eauto. }
  { intro C; inversion C; eauto. }
Qed.

Theorem module_le_spec : forall a b,
    Bool.reflect (sub_module a b) (module_le a b).
Proof.
  intros. generalize (module_le_sound a b).
  destruct (module_le a b); constructor; eauto.
Qed.

#[global]
Instance sub_module_dec : RelDecision sub_module :=
  fun l r => match module_le l r as X
                return (if X then sub_module l r else ~sub_module l r) -> {_} + {_}
          with
          | true => fun pf => left pf
          | false => fun pf => right pf
          end (module_le_sound l r).

Lemma sub_module_preserves_globdecl {m1 m2 gn g1} :
  sub_module m1 m2 ->
  m1.(types) !! gn = Some g1 ->
  ∃ g2, m2.(types) !! gn = Some g2 ∧ GlobDecl_ler g1 g2.
Proof. move=>/types_compat + Heq => /(_ _ _ Heq). eauto. Qed.

Lemma sub_modules_agree_globdecl tu1 tu2 tu3 nm gd1 gd2 :
  sub_module tu1 tu3 ->
  sub_module tu2 tu3 ->
  tu1.(types) !! nm = Some gd1 ->
  tu2.(types) !! nm = Some gd2 ->
  GlobDecl_ler gd1 gd2 \/ GlobDecl_ler gd2 gd1.
Proof.
  move=> Hs1 Hs2
    /(sub_module_preserves_globdecl Hs1) [] gd3 [Hlook Hl1]
    /(sub_module_preserves_globdecl Hs2) [] ? [? Hl2]; simplify_eq.
  exact: GlobDecl_ler_join.
Qed.

Lemma sub_module_preserves_gstruct m1 m2 gn st :
  sub_module m1 m2 ->
  m1.(types) !! gn = Some (Gstruct st) ->
  m2.(types) !! gn = Some (Gstruct st).
Proof.
  move=> Hsub /(sub_module_preserves_globdecl Hsub) {Hsub m1 m2} [g2 [->]].
  destruct g2 => //=. intros; do_bool_decide; subst; smash.
Qed.

Lemma sub_module_preserves_gunion m1 m2 gn un :
  sub_module m1 m2 ->
  m1.(types) !! gn = Some (Gunion un) ->
  m2.(types) !! gn = Some (Gunion un).
Proof.
  move=> Hsub /(sub_module_preserves_globdecl Hsub) {Hsub m1 m2} [g2 [->]].
  destruct g2 => //=; smash.
Qed.

(* For enums, [names1] and [names2] need not be related, as specified by [GlobDecl_le].
TODO: https://eel.is/c++draft/basic.def.odr#13 restricts this to anonymous enums. *)
Lemma sub_module_preserves_genum m1 m2 gn ty names1 :
  sub_module m1 m2 ->
  m1.(types) !! gn = Some (Genum ty names1) ->
  exists names2, m2.(types) !! gn = Some (Genum ty names2).
Proof.
  move=> Hsub /(sub_module_preserves_globdecl Hsub) {Hsub m1 m2} [g2 [->]].
  destruct g2 => //=; smash.
Qed.

Lemma sub_module_preserves_gconstant m1 m2 gn t e :
  sub_module m1 m2 ->
  m1.(types) !! gn = Some (Gconstant t (Some e)) ->
  m2.(types) !! gn = Some (Gconstant t (Some e)).
Proof.
  move=> Hsub /(sub_module_preserves_globdecl Hsub) {Hsub m1 m2} [g2 [->]].
  rewrite /GlobDecl_ler /GlobDecl_le; smash.
Qed.

Lemma sub_module_preserves_gtypedef m1 m2 gn t :
  sub_module m1 m2 ->
  m1.(types) !! gn = Some (Gtypedef t) ->
  m2.(types) !! gn = Some (Gtypedef t).
Proof.
  move=> Hsub /(sub_module_preserves_globdecl Hsub) [g2 [->]].
  destruct g2 => //=; intros; smash.
Qed.

#[global] Instance byte_order_proper : Proper (sub_module ==> eq) byte_order.
Proof. by destruct 1. Qed.
#[global] Instance byte_order_flip_proper : Proper (flip sub_module ==> eq) byte_order.
Proof. by destruct 1. Qed.


Lemma complete_type_respects_sub_module tt1 tt2 t :
  sub_module tt2 tt1 ->
  complete_type tt2.(types) t -> complete_type tt1.(types) t.
Proof. move=> /types_compat Hsub Hct. exact: complete_type_respects_sub_table. Qed.


(* [class_compatible a b c] states that translation units [a] and [b] have
   the same definitions for the class [cls] (including all transitive
   base classes)

   this is necessary, e.g. when code in translation unit [a] wants to call
   via a virtual table that was constructed in translation unit [b]
 *)
Inductive class_compatible (a b : translation_unit) (cls : name) : Prop :=
| Class_compat {st}
               (_ : a.(types) !! cls = Some (Gstruct st))
               (_ : b.(types) !! cls = Some (Gstruct st))
               (_ : forall base, In base (map fst st.(s_bases)) ->
                            class_compatible a b base).

#[local]
Lemma arguments_same xs : forall ys,
    map (λ b : ident * type, drop_qualifiers (normalize_type b.2)) xs = map (λ b : ident * type, drop_qualifiers (normalize_type b.2)) ys ->
    map (λ t : type, to_arg_type (normalize_type t)) xs.*2 = map (λ t : type, to_arg_type (normalize_type t)) ys.*2.
Proof.
  induction xs; destruct ys; simpl; intros; try congruence.
  inversion H; clear H; subst.
  f_equal; eauto.
  revert H1; clear.
  rewrite /to_arg_type. rewrite !qual_norm_decompose_type.
  rewrite !drop_qualifiers_decompose_type.
  destruct (decompose_type (normalize_type a.2)), (decompose_type (normalize_type p.2)); simpl in *; intros; subst.
  auto.
Qed.

Lemma type_of_value_ObjValue_ler a b : ObjValue_ler a b -> type_of_value a = type_of_value b.
Proof.
  destruct a, b; simpl; try congruence;
    repeat first [ case_bool_decide | case_match ]; subst; try congruence; simpl; eauto.
  all: intros; rewrite /type_of_value/=; try congruence.
  { f_equal. f_equal; eauto using arguments_same. }
  { f_equal. f_equal; eauto.
    f_equal; eauto using arguments_same.
    congruence. }
  { f_equal. f_equal; eauto.
    f_equal; eauto using arguments_same. congruence. }
Qed.
