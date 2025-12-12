(*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import elpi.apps.locker.locker.
Require Import bluerock.prelude.base.
Require Export bluerock.prelude.option.
Require Import bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.semantics.genv.

Definition GlobDecl_size_of (g : GlobDecl) : option N :=
  match g with
  | Gstruct s => Some s.(s_size)
  | Gunion u => Some u.(u_size)
  | Genum t _ =>
    match drop_qualifiers t with
    | Tchar_ sz => Some $ char_type.bytesN sz
    | Tnum sz _ => Some $ int_rank.bytesN sz
    | Tbool => Some 1%N
    | _ => None
    end
  | _ => None
  end.
Definition GlobDecl_align_of (g : GlobDecl) : option N :=
  match g with
  | Gstruct s => Some s.(s_alignment)
  | Gunion u => Some u.(u_alignment)
  | Genum t _ =>
    match drop_qualifiers t with
    | Tchar_ sz => Some $ char_type.bytesN sz
    | Tnum sz _ => Some $ int_rank.bytesN sz
    | Tbool => Some 1%N
    | _ => None
    end
  | _ => None
  end.


#[global] Instance proper_GlobDecl_size_of: Proper (GlobDecl_ler ==> Roption_leq eq) GlobDecl_size_of.
Proof.
  rewrite /GlobDecl_size_of/GlobDecl_ler/GlobDecl_le => x y Heq.
  do 2 case_match; subst; try contradiction; try constructor.
  case_bool_decide; subst; eauto. contradiction.
  case_bool_decide; subst; eauto. contradiction.
  case_bool_decide; subst; eauto. case_match; constructor; eauto. contradiction.
Qed.
#[global] Instance proper_GlobDecl_align_of: Proper (GlobDecl_ler ==> Roption_leq eq) GlobDecl_align_of.
Proof.
  rewrite /GlobDecl_size_of/GlobDecl_ler/GlobDecl_le => x y Heq.
  do 2 case_match; subst; try contradiction; try constructor.
  case_bool_decide; subst; eauto. contradiction.
  case_bool_decide; subst; eauto. contradiction.
  case_bool_decide; subst; eauto. simpl. case_match; constructor; eauto. contradiction.
Qed.

(** * sizeof *)
(** The size of a C++ object.
    This is *not* the same as the semantics of the <<sizeof()>> operator
    because <<sizeof(int&)>> is actually <<sizeof(int)>> whereas
    [size_of (Tref Tint)] is the size of the reference.

    Also, [size_of] is well-defined even in case of overflow, so many users need
    bound-checking; see for instance [wp_operand_sizeof].
 *)
Fixpoint size_of (resolve : genv) (t : type) : option N :=
  match t with
  | Tptr _ => Some (pointer_size resolve)
  | Tref _ => None
  | Trv_ref _ => None
  | Tnum sz _ => Some (int_rank.bytesN sz)
  | Tchar_ ct => Some (char_type.bytesN ct)
  | Tvoid => None
  | Tarray t n => N.mul n <$> size_of resolve t
  | Tincomplete_array _ => None
  | Tvariable_array _ _ => None
  | Tnamed nm => glob_def resolve nm ≫= GlobDecl_size_of
  | Tenum nm => glob_def resolve nm ≫= GlobDecl_size_of
  | Tfunction _ => None
  | Tbool => Some 1
  | Tmember_pointer _ _ => None (* TODO these are not well supported right now *)
  | Tqualified _ t => size_of resolve t
  | Tnullptr => Some (pointer_size resolve)
  | Tfloat_ sz => Some (float_type.bytesN sz)
  | Tarch sz _ => bitsize.bytesN <$> sz
  | Tunsupported _ => None
  | Tdecltype _
  | Texprtype _
  | Tparam _
  | Tresult_param _
  | Tresult_global _
  | Tresult_unop _ _
  | Tresult_binop _ _ _
  | Tresult_parenlist _ _
  | Tresult_member _ _
  | Tresult_call _ _
  | Tresult_member_call _ _ _
  | Tauto => None
  end%N.

(* [size_of] result can overflow: *)
Goal forall σ, size_of σ (Tarray Tchar (2^128)) = Some (2^128)%N.
Proof. by []. Abort.
(* [size_of] result can overflow, even with in-bounds arguments: *)
Goal forall σ, size_of σ (Tarray Tlonglong (2^61)) = Some (2^64)%N.
Proof. by []. Abort.

#[global] Instance Proper_size_of
  : Proper (genv_leq ==> eq ==> Roption_leq eq) (@size_of).
Proof.
  intros ?? Hle ? t ->; induction t; simpl; (try constructor) => //.
  all: try exact: pointer_size_proper.
  - by destruct IHt; constructor; subst.
(*  - rewrite /glob_def.
    generalize (types_compat _ _ (tu_le Hle) gn).
    destruct (types (genv_tu x) !! gn) eqn:Heq; simpl.
    { intro H; destruct (H _ Heq) as [?[Heq' ?]].
      rewrite Heq' /=.
      by eapply proper_GlobDecl_size_of. }
    { intros. constructor. }
  - rewrite /glob_def.
    generalize (types_compat _ _ (tu_le Hle) gn).
    destruct (types (genv_tu x) !! gn) eqn:Heq; simpl.
    { intro H; destruct (H _ Heq) as [?[Heq' ?]].
      rewrite Heq' /=.
      by eapply proper_GlobDecl_size_of. }
    { intros. constructor. }
*)
  - rewrite /glob_def. move: Hle => [[ /(_ gn) Hle _] _ _].
    revert Hle.
    case: (types (genv_tu x) !! gn); simpl; try constructor.
    move => ? /(_ _ eq_refl) [g2 [-> HH]] /=.
    exact: proper_GlobDecl_size_of.
  - rewrite /glob_def. move: Hle => [[ /(_ gn) Hle _] _ _].
    revert Hle.
    case: (types (genv_tu x) !! gn); simpl; try constructor.
    move => ? /(_ _ eq_refl) [g2 [-> HH]] /=.
    exact: proper_GlobDecl_size_of.
  - by destruct osz; constructor.
Qed.

Theorem size_of_int : forall {c : genv} s w,
    @size_of c (Tnum w s) = Some (int_rank.bytesN w).
Proof. reflexivity. Qed.
Theorem size_of_char : forall {c : genv} s,
    @size_of c (Tchar_ s) = Some (char_type.bytesN s).
Proof. reflexivity. Qed.
Theorem size_of_bool : forall {c : genv},
    @size_of c Tbool = Some 1%N.
Proof. reflexivity. Qed.
Theorem size_of_pointer : forall {c : genv} t,
    @size_of c (Tptr t) = Some (pointer_size c).
Proof. reflexivity. Qed.
Theorem size_of_qualified : forall {c : genv} t q,
    @size_of c t = @size_of c (Tqualified q t).
Proof. reflexivity. Qed.
Theorem size_of_array_0 : forall {c : genv} t sz,
    @size_of c t = Some sz ->
    @size_of c (Tarray t 0) = Some 0%N.
Proof. intros; simpl. by rewrite H. Qed.

Theorem size_of_array_shatter : forall {c : genv} ty n sz,
    @size_of c (Tarray ty n) = Some sz <-> exists sz', (sz = n * sz')%N /\ @size_of c ty = Some sz' /\ @size_of c (Tarray ty n) = Some (n * sz')%N.
Proof.
  simpl. intros. destruct (size_of c ty) => /=; split; intros H.
  - inversion H; subst; eauto.
  - by destruct H as [? [? [H1 H2]]]; inversion H1; inversion H2; subst.
  - by inversion H.
  - by destruct H as [? [? [? ?]]]; discriminate.
Qed.

Theorem size_of_array_pos : forall {c : genv} t n sz,
    (0 < n)%N ->
    @size_of c t = Some sz <-> @size_of c (Tarray t n) = Some (n * sz)%N.
Proof.
  simpl. intros. destruct (size_of c t) => /=; split; try congruence.
  inversion 1. f_equal. apply N.mul_cancel_l in H2.  auto. lia.
Qed.

Theorem size_of_array : forall {c : genv} t n sz,
    @size_of c t = Some sz -> @size_of c (Tarray t n) = Some (n * sz)%N.
Proof.
  simpl. intros. destruct (size_of c t) => /=; try congruence.
Qed.

Lemma size_of_Tmut : forall {c} t,
    @size_of c t = @size_of c (Tmut t).
Proof. reflexivity. Qed.

Lemma size_of_Tconst : forall {c} t ,
    @size_of c t = @size_of c (Tconst t).
Proof. reflexivity. Qed.

(* XXX: since size_of simplifies eagerly, this might be hard to apply, so you
might need to inline the proof. *)
Lemma size_of_genv_compat tu σ gn st
      (Hσ : tu ⊧ σ)
      (Hl : tu.(types) !! gn = Some (Gstruct st)) :
  size_of σ (Tnamed gn) = GlobDecl_size_of (Gstruct st).
Proof. by rewrite /= (glob_def_genv_compat_struct st Hl). Qed.

Lemma size_of_erase_qualifiers σ ty :
  size_of σ (erase_qualifiers ty) = size_of σ ty.
Proof. induction ty => //=. by rewrite IHty. Qed.
Lemma size_of_drop_qualifiers σ ty :
  size_of σ (drop_qualifiers ty) = size_of σ ty.
Proof. by induction ty. Qed.

(** [SizeOf ty n] means that C++ type [ty] has size [n] bytes *)
Class SizeOf {σ : genv} (ty : type) (n : N) : Prop :=
  size_of_spec : size_of σ ty = Some n.
#[global] Hint Mode SizeOf - + - : typeclass_instances.

#[global] Instance SizeOf_mono :
  Proper (genv_leq ==> eq ==> eq ==> impl) (@SizeOf).
Proof.
  rewrite /SizeOf=>σ1 σ2 Hσ t1 t2 Ht n ? <- ?.
  by destruct (Proper_size_of _ _ Hσ _ _ Ht); simplify_eq.
Qed.

#[global] Instance array_size_of {σ : genv} ty a n b :
  SizeOf ty a ->
  TCEq (n * a)%N b ->
  SizeOf (Tarray ty n) b.
Proof.
  rewrite /SizeOf TCEq_eq=>Hty <-.
  cbn. by rewrite Hty.
Qed.

#[global] Instance named_struct_size_of tu σ gn st n :
  genv_compat tu σ ->
  TCEq (tu.(types) !! gn) (Some (Gstruct st)) ->
  TCEq st.(s_size) n ->
  SizeOf (Tnamed gn) n.
Proof.
  rewrite /SizeOf !TCEq_eq=>? /glob_def_genv_compat_struct Htu <-.
  cbn. by rewrite Htu.
Qed.

#[global] Instance named_union_size_of tu σ gn u n :
  genv_compat tu σ ->
  TCEq (tu.(types) !! gn) (Some (Gunion u)) ->
  TCEq u.(u_size) n ->
  SizeOf (Tnamed gn) n.
Proof.
  rewrite /SizeOf !TCEq_eq=>? /glob_def_genv_compat_union Htu <-.
  cbn. by rewrite Htu.
Qed.

#[global] Instance bool_size_of {σ : genv} : SizeOf Tbool 1.
Proof. done. Qed.

(* TODO?: consider using [SizeOf (Tnum sz sgn) (bytesN sz)]. *)
#[global] Instance int_size_of {σ : genv} sz sgn n :
  TCEq (int_rank.bytesN sz) n -> SizeOf (Tnum sz sgn) n.
Proof. by rewrite /SizeOf TCEq_eq=><-. Qed.

(* TODO?: consider using [SizeOf (Tnum sz sgn) (char_type.bytesN ct)]. *)
#[global] Instance char_size_of {σ' : genv} ct n :
  TCEq (char_type.bytesN ct) n -> SizeOf (Tchar_ ct) n.
Proof. by rewrite /SizeOf TCEq_eq=><-. Qed.

#[global] Instance qualified_size_of {σ : genv} qual ty n :
  SizeOf ty n -> SizeOf (Tqualified qual ty) n.
Proof. done. Qed.

#[global] Instance ptr_size_of {σ : genv} ty n :
  TCEq (pointer_size σ) n -> SizeOf (Tptr ty) n.
Proof. by rewrite /SizeOf TCEq_eq=><-. Qed.

#[global] Instance arch_size_of {σ : genv} sz name n :
  TCEq (bitsize.bytesN sz) n -> SizeOf (Tarch (Some sz) name) n.
Proof. by rewrite /SizeOf TCEq_eq=><-. Qed.

(** [HasSize ty] means that C++ type [ty] has a defined size *)
Class HasSize {σ : genv} (ty : type) : Prop :=
  has_size : is_Some (size_of σ ty).
#[global] Hint Mode HasSize - + : typeclass_instances.
#[global] Arguments has_size {_} _ {_} : assert.

#[global] Instance HasSize_mono :
  Proper (genv_leq ==> eq ==> impl) (@HasSize).
Proof.
  rewrite /HasSize=>σ1 σ2 Hσ t1 t2 Ht H.
  destruct (Proper_size_of _ _ Hσ _ _ Ht).
  - exfalso. exact: is_Some_None.
  - by simplify_eq.
Qed.

#[global] Instance size_of_has_size {σ : genv} ty n :
  SizeOf ty n -> HasSize ty.
Proof.
  intros. rewrite /HasSize size_of_spec. by eexists.
Qed.

(** [sizeof ty : N] is the size of C++ type [ty] (if it has a size) *)
Definition sizeof {σ : genv} (ty : type) `{!HasSize ty} : N :=
  is_Some_proj (has_size ty).

Lemma sizeof_spec {σ : genv} ty `{Hsz : !HasSize ty} :
  size_of σ ty = Some (sizeof ty).
Proof.
  rewrite/sizeof/has_size. by destruct Hsz as [sz ->].
Qed.

(** [offset_of] *)

Fixpoint find_assoc_list {K T} `{!EqDecision K} (f : K) (fs : list (K * T)) : option T :=
  match fs with
  | nil => None
  | (f',v) :: fs =>
    if decide (f = f') then
      Some v
    else find_assoc_list f fs
  end%list.

Lemma find_assoc_list_elem_of {K T} `{!EqDecision K} (base : K) xs :
  (∃ v, (base, v) ∈ xs) ->
  ∃ y, find_assoc_list (T := T) base xs = Some y.
Proof.
  move=>[v]. elim: xs => /= [/elem_of_nil //|[k w] xs IH]
    /elem_of_cons [|] Hin; simplify_eq.
  { rewrite decide_True; eauto. }
  case_decide; eauto.
Qed.

#[local] Close Scope nat_scope.
#[local] Open Scope Z_scope.
(* note: we expose the fact that reference fields are compiled to pointers,
   so the [offset_of] a reference field is the offset of the pointer.
 *)
Definition offset_of (σ : genv) (t : globname) (f : atomic_name) : option Z :=
  match glob_def σ t with
  | Some (Gstruct s) =>
    find_assoc_list f (List.map (fun m => (m.(mem_name),m.(mem_layout).(li_offset) / 8)) s.(s_fields))
  | Some (Gunion u) =>
    find_assoc_list f (List.map (fun m => (m.(mem_name),m.(mem_layout).(li_offset) / 8)) u.(u_fields))
  | _ => None
  end.

Definition parent_offset_tu (tu : translation_unit) (derived : name) (base : name) : option Z :=
  match tu.(types) !! derived with
  | Some (Gstruct s) => find_assoc_list base (List.map (fun '(s,l) => (s,l.(li_offset) / 8)) s.(s_bases))
  | _ => None
  end.
(* We hide whether [genv_tu] exists. *)
mlock Definition parent_offset σ derived base := parent_offset_tu σ.(genv_tu) derived base.
Notation directly_derives_tu tu derived base := (is_Some (parent_offset_tu tu derived base)).
Notation directly_derives σ derived base := (is_Some (parent_offset σ derived base)).

Lemma find_assoc_list_parent_offset tu derived st base li :
  tu.(types) !! derived = Some (Gstruct st) ->
  (base, li) ∈ st.(s_bases) ->
  ∃ z, parent_offset_tu tu derived base = Some z.
Proof.
  rewrite /parent_offset_tu => -> Hin.
  apply /find_assoc_list_elem_of.
  eexists; apply /elem_of_list_fmap; by exists (base, li).
Qed.

Lemma parent_offset_genv_compat {σ tu derived base z} {Hσ : tu ⊧ σ} :
  parent_offset_tu tu derived base = Some z ->
  parent_offset σ derived base = Some z.
Proof.
  rewrite parent_offset.unlock /parent_offset_tu -/(glob_def σ derived).
  case E: (tu.(types) !! derived) => [ gd //= | // ]; destruct gd => //.
  by erewrite glob_def_genv_compat_struct.
Qed.

(** * alignof *)

(* [align_of t] returns the alignment of the type [t].
 *)
Parameter align_of : forall {σ : genv} (t : type), option N.
Section with_genv.
  Context {σ : genv}.

  (* All alignments are in integral power of 2.
     See <https://eel.is/c++draft/basic.memobj#basic.align-4>
   *)
  Axiom align_of_power_of_two : forall t al, align_of t = Some al -> exists n, al = N.pow 2 n.

  (** If [size_of] is defined, [align_of] must divide [size_of]. *)
  Axiom align_of_size_of' : forall (t : type) sz,
      size_of σ t = Some sz ->
      (exists al, align_of t = Some al /\ al <> 0 /\ (al | sz))%N.

  Lemma align_of_size_of (t : type) sz :
      size_of σ t = Some sz ->
      exists al, align_of t = Some al /\
            (* size is a multiple of alignment *)
            (sz mod al = 0)%N.
  Proof.
    move=>/align_of_size_of' [al [? [? /N.Lcm0.mod_divide ?]]].
    eauto.
  Qed.

  (* The alignment of named types are recorded in the translation unit *)
  Axiom align_of_named : forall nm,
    align_of (Tnamed nm) =
    glob_def σ nm ≫= GlobDecl_align_of.

  Axiom align_of_array : forall (ty : type) n,
      align_of (Tarray ty n) = align_of ty.
  Axiom align_of_incomplete_array : forall (ty : type),
      align_of (Tincomplete_array ty) = align_of ty.
  Axiom align_of_variable_array : forall (ty : type) e,
      align_of (Tvariable_array ty e) = align_of ty.

  Axiom align_of_erase_qualifiers : ∀ t,
      align_of (erase_qualifiers t) = align_of t.

  Lemma align_of_char : align_of Tchar = Some 1%N.
  Proof.
    destruct (align_of_size_of' Tchar 1 (size_of_char _)) as [?[->[?Hd]]].
    by f_equal; eapply N.divide_1_r.
  Qed.
  Lemma align_of_uchar : align_of Tuchar = Some 1%N.
  Proof.
    destruct (align_of_size_of' Tuchar 1 (size_of_int _ _)) as [?[->[?Hd]]].
    by f_equal; eapply N.divide_1_r.
  Qed.
  Lemma align_of_schar : align_of Tschar = Some 1%N.
  Proof.
    destruct (align_of_size_of' Tschar 1 (size_of_int _ _)) as [?[->[?Hd]]].
    by f_equal; eapply N.divide_1_r.
  Qed.

  (* NOTE: the following three axioms equate the size and alignment of
     certain fundamental types. This does not seem to be sanctioned by
     the standard, but does seem to be true in practice.
   *)
  Axiom UNSAFE_align_is_size_int : forall sz sgn, align_of (Tnum sz sgn) = size_of σ (Tnum sz sgn).
  Axiom UNSAFE_align_is_size_char : forall c, align_of (Tchar_ c) = size_of σ (Tchar_ c).
  Axiom UNSAFE_align_is_size_ptr : forall t, align_of (Tptr t) = size_of σ (Tptr t).

  Lemma align_of_qualified : ∀ t q,
      align_of (Tqualified q t) = align_of t.
  Proof.
    intros.
    rewrite -{1}align_of_erase_qualifiers. simpl. by rewrite align_of_erase_qualifiers.
  Qed.

  Axiom Proper_align_of : Proper (genv_leq ==> eq ==> Roption_leq eq) (@align_of).
  #[global] Existing Instance Proper_align_of.

  Lemma align_of_genv_compat tu gn st
        (Hσ : tu ⊧ σ)
        (Hl : tu.(types) !! gn = Some (Gstruct st)) :
    align_of (Tnamed gn) = GlobDecl_align_of (Gstruct st).
  Proof. by rewrite /= align_of_named (glob_def_genv_compat_struct st Hl). Qed.

  Lemma align_of_genv_leq σ1 σ2 ty align :
    @align_of σ1 ty = Some align ->
    genv_leq σ1 σ2 ->
    @align_of σ2 ty = Some align.
  Proof.
    move=> /[swap] /Proper_align_of /(_ ty ty eq_refl) /=.
    by inversion 1; naive_solver.
  Qed.
End with_genv.
