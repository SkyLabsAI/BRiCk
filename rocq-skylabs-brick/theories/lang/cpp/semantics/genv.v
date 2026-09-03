(*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Export skylabs.lang.cpp.syntax.
Require Export skylabs.lang.cpp.semantics.sub_module.

(* NOTE:
    This constant should be provided by the C++ compiler / runtime.
    It defines the minimal alignment, and it must be at least as
    aligned as pointers.
  *)
Definition STDCPP_DEFAULT_NEW_ALIGNMENT : N := 16.

(**
A [genv] describes the dynamic semantics of a potentially incomplete program,
comprising one or more C++ translation units.
Most proofs only quantify over a single `σ : genv`, representing the complete
program being verified.

The interface includes:
- an injection of C++ translation units to genvs (which represents compilation).
- and a composition of [genv]s (which represents linking).

Today, we compose [genv]s by composing [translation_unit]s, but this is an
implementation detail that might change (see FM-2738).

A [genv] contains the result of linking translation units, plus any additional
information supplied by compiler/linker/loader/...

A value of type [translation_unit] names a concrete source translation unit and
can reduce accordingly. A value [σ : genv] instead names the linked program
environment. To keep verification modular, proofs abstract over [σ : genv] and
assume compatibility with the concrete translation units being verified, rather
than reducing through the linked program representation directly.

If we add support for dynamic linking, additional [genv]s might be involved.

If we want to do things like word-size agnostic verification, then
information about sizes etc. would need to move in here as well.

TODO: seal this?
*)
Record genv : Type :=
{ genv_tu : translation_unit
  (* ^ Implementation detail: the result of merging all the [translation_unit]s
  in the program. Might be replaced when fixing FM-2738. *)
; genv_tu_canonical : TU.canonical genv_tu = genv_tu
  (* ^ Linking produces a location-free translation unit.  Recording that
     invariant lets public semantic relations use [TU.canonical] while
     operational lookups keep using the linked unit directly. *)
}.

Existing Class genv.

Definition genv_view (g : genv) : SemanticTU.t :=
  SemanticTU.of_canonical g.(genv_tu).

Definition genv_abi (g : genv) : abi.t :=
  g.(genv_tu).(abi).
Definition pointer_size_bitsize (g : genv) : bitsize :=
  abi.pointer_size_bitsize (genv_abi g).
Definition char_signed (g : genv) : signed :=
  (genv_abi g).(abi.char_signed).
Definition wchar_signed (g : genv) : signed :=
  (genv_abi g).(abi.wchar_signed).
Definition genv_byte_order (g : genv) : endian :=
  (genv_abi g).(abi.byte_order).
Definition pointer_size (g : genv) := bitsize.bytesN (pointer_size_bitsize g).
Definition genv_type_table (g : genv) : type_table :=
  SemanticTU.types (genv_view g).

Definition signedness_of_char (σ : genv) (ct : char_type) : signed :=
  abi.signedness_of_char (genv_abi σ) ct.

(** [equivalent_int_type g ct] is the integral type that is equivalent
    (in rank and signedness) of [ct].
 *)
Definition equivalent_int_type (g : genv) (ct : char_type) : integral_type.t :=
  abi.equivalent_int_type (genv_abi g) ct.

(** * global environments *)

(** [genv_leq a b] states that [b] is an extension of [a] *)
Record genv_leq {l r : genv} : Prop :=
{ tu_le : view_sub_module (genv_view l) (genv_view r) }.
Arguments genv_leq _ _ : clear implicits.

#[global] Instance PreOrder_genv_leq : PreOrder genv_leq.
Proof.
  constructor.
  { constructor; auto; reflexivity. }
  { red. destruct 1; destruct 1; constructor. etransitivity; eauto. }
Qed.
#[global] Instance: RewriteRelation genv_leq := {}.

Definition genv_eq (l r : genv) : Prop :=
  genv_leq l r /\ genv_leq r l.

#[global] Instance genv_tu_proper : Proper (genv_leq ==> sub_module) genv_tu.
Proof. intros ?? [H]. exact H. Qed.
#[global] Instance genv_tu_flip_proper :
    Proper (flip genv_leq ==> flip sub_module) genv_tu.
Proof. intros ?? [H]. exact H. Qed.

(* Sadly, neither instance is picked up by [f_equiv]. *)
#[global] Instance genv_abi_proper : Proper (genv_leq ==> eq) genv_abi.
Proof.
  intros l r [H].
  unfold view_sub_module, genv_view, SemanticTU.of_canonical in H.
  apply abi_compat in H. exact H.
Qed.
#[global] Instance genv_abi_flip_proper : Proper (flip genv_leq ==> eq) genv_abi.
Proof.
  intros l r [H].
  unfold view_sub_module, genv_view, SemanticTU.of_canonical in H.
  symmetry. apply abi_compat in H. exact H.
Qed.
#[global] Instance pointer_size_bitsize_proper : Proper (genv_leq ==> eq) pointer_size_bitsize.
Proof. intros ?? Hle. by rewrite /pointer_size_bitsize (genv_abi_proper _ _ Hle). Qed.
#[global] Instance pointer_size_bitsize_flip_proper : Proper (flip genv_leq ==> eq) pointer_size_bitsize.
Proof. intros ?? Hle. by rewrite /pointer_size_bitsize (genv_abi_flip_proper _ _ Hle). Qed.
#[global] Instance pointer_size_proper : Proper (genv_leq ==> eq) pointer_size.
Proof. unfold pointer_size; intros ???. f_equiv. exact: pointer_size_bitsize_proper. Qed.
#[global] Instance pointer_size_flip_proper : Proper (flip genv_leq ==> eq) pointer_size.
Proof. unfold pointer_size; intros ???. f_equiv. exact: pointer_size_bitsize_flip_proper. Qed.

#[global] Instance genv_byte_order_proper : Proper (genv_leq ==> eq) genv_byte_order.
Proof. intros ?? Hle. by rewrite /genv_byte_order (genv_abi_proper _ _ Hle). Qed.
#[global] Instance genv_byte_order_flip_proper : Proper (flip genv_leq ==> eq) genv_byte_order.
Proof. intros ?? Hle. by rewrite /genv_byte_order (genv_abi_flip_proper _ _ Hle). Qed.
(* this states that the [genv] is compatible with the given [translation_unit]
 * it essentially means that the [genv] records all the types from the
 * compilation unit and that the [genv] contains addresses for all globals
 * defined in the [translation_unit]
 *)
(** Semantic consumers ignore source-location wrappers while generated
    translation units retain them for diagnostics and tooling. *)
Class genv_compat {tu : translation_unit} {g : genv} : Prop :=
  Build_semantic_genv_compat
  { tu_compat : view_sub_module (SemanticTU.of_tu tu) (genv_view g) }.
Arguments genv_compat _ _ : clear implicits.
Infix "⊧" := genv_compat (at level 1).

(** Byte-order compatibility is weaker than full semantic compatibility.
    Its legacy constructor name preserves the long-standing proof pattern
    [apply Build_genv_compat; reflexivity] for the linked TU itself. *)
Class genv_abi_compat (tu : translation_unit) (g : genv) : Prop :=
  Build_genv_abi_compat
  { genv_byte_order_compat : genv_byte_order g = byte_order tu }.

(** A legacy constructor name for proofs that only need byte-order
    compatibility.  Keeping this as a definition, rather than as the class
    constructor, prevents [eauto] from inventing an unrelated translation
    unit when a semantic compatibility witness is already in scope. *)
Definition Build_genv_compat tu g
    (H : genv_byte_order g = byte_order tu) : genv_abi_compat tu g.
Proof. by constructor. Defined.

#[global] Instance genv_compat_abi tu g :
    genv_compat tu g -> genv_abi_compat tu g.
Proof.
  move=>[H]. constructor.
  apply byte_order_flip_proper in H. exact H.
Qed.
#[global] Hint Resolve genv_compat_abi : core.

Theorem genv_byte_order_tu tu g :
    genv_abi_compat tu g ->
    genv_byte_order g = byte_order tu.
Proof. by destruct 1. Qed.

Theorem genv_compat_submodule : forall m σ, m ⊧ σ ->
  sub_module (TU.canonical m) σ.(genv_tu).
Proof. by destruct 1. Qed.

Theorem genv_compat_semantic_submodule : forall m σ, m ⊧ σ ->
  semantic_sub_module m σ.(genv_tu).
Proof.
  intros m σ Hcompat.
  rewrite semantic_sub_module_eq. unfold view_sub_module.
  change (sub_module (TU.canonical m) (TU.canonical σ.(genv_tu))).
  rewrite σ.(genv_tu_canonical).
  exact (genv_compat_submodule m σ Hcompat).
Qed.
#[global] Hint Resolve genv_compat_semantic_submodule : core.

#[global] Instance genv_compat_proper :
    Proper (flip semantic_sub_module ==> genv_leq ==> impl) genv_compat.
Proof.
  intros tu1 tu2 Htu g1 g2 [Hg] [Hcompat]. constructor.
  try rewrite semantic_sub_module_eq in Htu.
  etransitivity; [exact Htu|].
  etransitivity; [exact Hcompat|exact Hg].
Qed.
#[global] Instance genv_compat_flip_proper :
    Proper (semantic_sub_module ==> flip genv_leq ==> flip impl) genv_compat.
Proof.
  intros tu1 tu2 Htu g1 g2 [Hg] [Hcompat]. constructor.
  try rewrite semantic_sub_module_eq in Htu.
  etransitivity; [exact Htu|].
  etransitivity; [exact Hcompat|exact Hg].
Qed.

Lemma module_le_genv_tu_models X σ :
  view_module_le (SemanticTU.of_tu X) (genv_view σ) ->
  X ⊧ σ.
Proof.
  move=> Hle. apply Build_semantic_genv_compat.
  have Hspec := view_module_le_spec (SemanticTU.of_tu X) (genv_view σ).
  case E: view_module_le in Hle; last contradiction.
  rewrite E in Hspec. by inversion Hspec.
Qed.

(** ** One Definition Rule

    The "one definition rule" states that if a single program ([σ : genv]) contains
    two translation units that both declare/define the same type, then those two
    type declarations/definitions are consistent. That is, they are either the same
    or one is a declaration and the other is a definition.

    Current limitations:
    - This does not (currently) account for visibility, e.g. with anonymous namespaces
    - This lemma only covers type declarations.
 *)
Lemma ODR {σ tu1 tu2} :
    tu1 ⊧ σ ->
    tu2 ⊧ σ -> forall nm gd1 gd2,
        SemanticTU.lookup_type (SemanticTU.of_tu tu1) nm = Some gd1 ->
        SemanticTU.lookup_type (SemanticTU.of_tu tu2) nm = Some gd2 ->
        GlobDecl_compat gd1 gd2.
Proof.
  move => [Hsub1] [Hsub2] nm gd1 gd2 H1 H2.
  have H1' := eq_trans
    (SemanticTU.lookup_type_spec (SemanticTU.of_tu tu1) nm) H1.
  have H2' := eq_trans
    (SemanticTU.lookup_type_spec (SemanticTU.of_tu tu2) nm) H2.
  apply Hsub1 in H1' as [gd1' [Hlookup1 H1']].
  apply Hsub2 in H2' as [gd2' [Hlookup2 H2']].
  rewrite Hlookup1 in Hlookup2. simplify_eq.
  by eapply GlobDecl_ler_join.
Qed.

(** TODO deprecate this in favor of inlining it *)
Definition glob_def (σ : genv) (gn : name) : option GlobDecl :=
  genv_type_table σ !! gn.

(*
Lemma glob_def_alt σ gn :
  glob_def σ gn = genv_type_table σ !! gn.
Proof. done. Qed.
*)

(* Supersedes glob_def_submodule *)
Lemma glob_def_genv_compat_struct {σ gn tu} {Hσ : tu ⊧ σ} st
  (Hl : SemanticTU.lookup_type (SemanticTU.of_tu tu) gn = Some (Gstruct st)) :
  glob_def σ gn = Some (Gstruct st).
Proof.
  have Hl' := eq_trans
    (SemanticTU.lookup_type_spec (SemanticTU.of_tu tu) gn) Hl.
  move: Hσ => /genv_compat_submodule Hsub.
  unfold view_sub_module in Hsub.
  unfold glob_def, genv_type_table, SemanticTU.types in *.
  exact: sub_module_preserves_gstruct Hsub Hl'.
Qed.

Lemma glob_def_genv_compat_union {σ gn tu} {Hσ : tu ⊧ σ} st
  (Hl : SemanticTU.lookup_type (SemanticTU.of_tu tu) gn = Some (Gunion st)) :
  glob_def σ gn = Some (Gunion st).
Proof.
  have Hl' := eq_trans
    (SemanticTU.lookup_type_spec (SemanticTU.of_tu tu) gn) Hl.
  move: Hσ => /genv_compat_submodule Hsub.
  unfold view_sub_module in Hsub.
  unfold glob_def, genv_type_table, SemanticTU.types in *.
  exact: sub_module_preserves_gunion Hsub Hl'.
Qed.

Lemma glob_def_genv_compat_enum {σ gn tu} {Hσ : tu ⊧ σ} ty brs
  (Hl : SemanticTU.lookup_type (SemanticTU.of_tu tu) gn = Some (Genum ty brs)) :
  exists brs', glob_def σ gn = Some (Genum ty brs').
Proof.
  have Hl' := eq_trans
    (SemanticTU.lookup_type_spec (SemanticTU.of_tu tu) gn) Hl.
  move: Hσ => /genv_compat_submodule Hsub.
  unfold view_sub_module in Hsub.
  unfold glob_def, genv_type_table, SemanticTU.types in *.
  exact: sub_module_preserves_genum Hsub Hl'.
Qed.

Lemma glob_def_genv_compat_constant {σ gn tu} {Hσ : tu ⊧ σ} ty e
  (Hl : SemanticTU.lookup_type (SemanticTU.of_tu tu) gn = Some (Gconstant ty (Some e))) :
  glob_def σ gn = Some (Gconstant ty (Some e)).
Proof.
  have Hl' := eq_trans
    (SemanticTU.lookup_type_spec (SemanticTU.of_tu tu) gn) Hl.
  move: Hσ => /genv_compat_submodule Hsub.
  unfold view_sub_module in Hsub.
  unfold glob_def, genv_type_table, SemanticTU.types in *.
  exact: sub_module_preserves_gconstant Hsub Hl'.
Qed.

(* XXX rename/deprecate? *)
Theorem subModuleModels a b σ :
    b ⊧ σ -> semantic_sub_module a b -> a ⊧ σ.
Proof. by intros ? ->. Qed.

(* TODO: [type_of_field] -- only needed in one place?
(** compute the type of a [class] or [union] field *)
Section type_of_field.
  Context {σ: genv}.

  Definition type_of_field (cls : globname) (f : field_name) : option type :=
    match σ.(genv_tu) !! cls with
    | None => None
    | Some (Gstruct st) =>
      match List.find (fun m => bool_decide (f = m.(mem_name))) st.(s_fields) with
      | Some m => Some m.(mem_type)
      | _ => None
      end
    | Some (Gunion u) =>
      match List.find (fun m => bool_decide (f = m.(mem_name))) u.(u_fields) with
      | Some m => Some m.(mem_type)
      | _ => None
      end
    | _ => None
    end.

  Definition type_of_path (from : globname) (p : InitPath) : option type :=
    match p with
    | InitThis => Some (Tnamed from)
    | InitField fn => type_of_field from fn
    | InitBase gn => Some (Tnamed gn)
    | InitIndirect ls i =>
      (* this is a little bit awkward because we assume the correctness of
         the type annotations in the path
       *)
      (fix go (from : globname) (ls : _) : option type :=
         match ls with
         | nil => type_of_field from i
         | (_, gn) :: ls => go gn ls
         end) from ls
    end.

End type_of_field.
*)
