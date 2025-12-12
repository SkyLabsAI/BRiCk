(*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.prelude.base.
Require Export bluerock.lang.cpp.syntax.
Require Export bluerock.lang.cpp.semantics.sub_module.

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

If we add support for dynamic linking, additional [genv]s might be involved.

If we want to do things like word-size agnostic verification, then
information about sizes etc. would need to move in here as well.

TODO: seal this?
*)
Record genv : Type :=
{ genv_tu : translation_unit
  (* ^ Implementation detail: the result of merging all the [translation_unit]s
  in the program. Might be replaced when fixing FM-2738. *)
; pointer_size_bitsize : bitsize
  (* ^ the size of a pointer *)
; char_signed : signed
  (* ^ whether or not `char` is signed or unsigned *)
; wchar_signed : signed
  (* ^ whether or not `wchar` is signed or unsigned *)
}.
Existing Class genv.
Definition genv_byte_order (g : genv) : endian :=
  g.(genv_tu).(byte_order).
Definition pointer_size (g : genv) := bitsize.bytesN (pointer_size_bitsize g).
Definition genv_type_table (g : genv) : type_table :=
  g.(genv_tu).(types).

Module integral_type.
  Record t : Set := mk { size : int_rank.t ; signedness : signed }.

  Coercion to_type (v : t) : type :=
    Tnum v.(size) v.(signedness).
End integral_type.
Coercion integral_type.to_type : integral_type.t >-> type.

Definition signedness_of_char (σ : genv) (ct : char_type) : signed :=
  match ct with
  | char_type.Cchar => σ.(char_signed)
  | char_type.Cwchar => σ.(wchar_signed)
  | _ => Unsigned
  end.

(** [equivalent_int_type g ct] is the integral type that is equivalent
    (in rank and signedness) of [ct].
 *)
#[local] Definition find_equiv (ct : char_type)
  (res := find (fun a => bool_decide (char_type.bitsN ct <= int_rank.bitsN a)%N) int_rank.ranks)
  : match res with
    | None => unit
    | Some _ => int_rank.t
    end :=
  match res as X return match X with
                        | None => unit
                        | Some _ => int_rank.t
                        end with
  | None => tt
  | Some x => x
  end.

Definition equivalent_int_type (g : genv) (ct : char_type) : integral_type.t :=
  let bits :=
    (* NOTE the setup here computes the appropriate type given the size
       constraints defined in [char_type.bitsN] and [int_type.bitsN] *)
    match ct with
    | char_type.Cchar => int_rank.Ichar
    | char_type.C8 => Evaluate (find_equiv char_type.C8)
    | char_type.C16 => Evaluate (find_equiv char_type.C16)
    | char_type.C32 => Evaluate (find_equiv char_type.C32)
    | char_type.Cwchar => Evaluate (find_equiv char_type.Cwchar)
    end
  in
  integral_type.mk bits (signedness_of_char g ct).

(** * global environments *)

(** [genv_leq a b] states that [b] is an extension of [a] *)
Record genv_leq {l r : genv} : Prop :=
{ tu_le : sub_module l.(genv_tu) r.(genv_tu)
; pointer_size_le : l.(pointer_size_bitsize) = r.(pointer_size_bitsize) }.
Arguments genv_leq _ _ : clear implicits.

#[global] Instance PreOrder_genv_leq : PreOrder genv_leq.
Proof.
  constructor.
  { constructor; auto; reflexivity. }
  { red. destruct 1; destruct 1; constructor; try etransitivity; eauto. }
Qed.
#[global] Instance: RewriteRelation genv_leq := {}.

Definition genv_eq (l r : genv) : Prop :=
  genv_leq l r /\ genv_leq r l.

#[global] Instance genv_tu_proper : Proper (genv_leq ==> sub_module) genv_tu.
Proof. solve_proper. Qed.
#[global] Instance genv_tu_flip_proper : Proper (flip genv_leq ==> flip sub_module) genv_tu.
Proof. solve_proper. Qed.

(* Sadly, neither instance is picked up by [f_equiv]. *)
#[global] Instance pointer_size_bitsize_proper : Proper (genv_leq ==> eq) pointer_size_bitsize.
Proof. solve_proper. Qed.
#[global] Instance pointer_size_bitsize_flip_proper : Proper (flip genv_leq ==> eq) pointer_size_bitsize.
Proof. by intros ?? <-. Qed.
#[global] Instance pointer_size_proper : Proper (genv_leq ==> eq) pointer_size.
Proof. unfold pointer_size; intros ???. f_equiv. exact: pointer_size_bitsize_proper. Qed.
#[global] Instance pointer_size_flip_proper : Proper (flip genv_leq ==> eq) pointer_size.
Proof. by intros ?? <-. Qed.

#[global] Instance genv_byte_order_proper : Proper (genv_leq ==> eq) genv_byte_order.
Proof. intros ???. apply sub_module.byte_order_proper. solve_proper. Qed.
#[global] Instance genv_byte_order_flip_proper : Proper (flip genv_leq ==> eq) genv_byte_order.
Proof. by intros ?? <-. Qed.
(* this states that the [genv] is compatible with the given [translation_unit]
 * it essentially means that the [genv] records all the types from the
 * compilation unit and that the [genv] contains addresses for all globals
 * defined in the [translation_unit]
 *)
Class genv_compat {tu : translation_unit} {g : genv} : Prop :=
{ tu_compat : sub_module tu g.(genv_tu) }.
Arguments genv_compat _ _ : clear implicits.
Infix "⊧" := genv_compat (at level 1).

Theorem genv_byte_order_tu tu g :
    tu ⊧ g ->
    genv_byte_order g = byte_order tu.
Proof. intros. apply byte_order_flip_proper, tu_compat. Qed.

Theorem genv_compat_submodule : forall m σ, m ⊧ σ -> sub_module m σ.(genv_tu).
Proof. by destruct 1. Qed.

#[global] Instance genv_compat_proper : Proper (flip sub_module ==> genv_leq ==> impl) genv_compat.
Proof.
  intros ?? Heq1 ?? [Heq2 _] [Heq3]; constructor.
  by rewrite Heq1 Heq3.
Qed.
#[global] Instance genv_compat_flip_proper : Proper (sub_module ==> flip genv_leq ==> flip impl) genv_compat.
Proof. solve_proper. Qed.

Lemma module_le_genv_tu_models X σ :
  module_le X (genv_tu σ) ->
  X ⊧ σ.
Proof.
  generalize (module_le_sound X (genv_tu σ)).
  unfold Is_true in *.
  case_match; try contradiction. intros.
  apply Build_genv_compat. assumption.
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
        tu1.(types) !! nm = Some gd1 ->
        tu2.(types) !! nm = Some gd2 ->
        GlobDecl_compat gd1 gd2.
Proof.
  move => [Hsub1] [Hsub2] nm gd1 gd2 H1 H2.
  apply Hsub1 in H1 as [gd1' [Hlookup1 H1]].
  apply Hsub2 in H2 as [gd2' [Hlookup2 H2]].
  rewrite Hlookup1 in Hlookup2. simplify_eq.
  by eapply GlobDecl_ler_join.
Qed.

(** TODO deprecate this in favor of inlining it *)
Definition glob_def (σ : genv) (gn : name) : option GlobDecl :=
  σ.(genv_tu).(types) !! gn.

(*
Lemma glob_def_alt σ gn :
  glob_def σ gn = genv_type_table σ !! gn.
Proof. done. Qed.
*)

(* Supersedes glob_def_submodule *)
Lemma glob_def_genv_compat_struct {σ gn tu} {Hσ : tu ⊧ σ} st
  (Hl : tu.(types) !! gn = Some (Gstruct st)) :
  glob_def σ gn = Some (Gstruct st).
Proof. move: Hσ Hl => /genv_compat_submodule. apply: sub_module_preserves_gstruct. Qed.

Lemma glob_def_genv_compat_union {σ gn tu} {Hσ : tu ⊧ σ} st
  (Hl : tu.(types) !! gn = Some (Gunion st)) :
  glob_def σ gn = Some (Gunion st).
Proof. move: Hσ Hl => /genv_compat_submodule. apply: sub_module_preserves_gunion. Qed.

Lemma glob_def_genv_compat_enum {σ gn tu} {Hσ : tu ⊧ σ} ty brs
  (Hl : tu.(types) !! gn = Some (Genum ty brs)) :
  exists brs', glob_def σ gn = Some (Genum ty brs').
Proof. move: Hσ Hl => /genv_compat_submodule. apply: sub_module_preserves_genum. Qed.

Lemma glob_def_genv_compat_constant {σ gn tu} {Hσ : tu ⊧ σ} ty e
  (Hl : tu.(types) !! gn = Some (Gconstant ty (Some e))) :
  glob_def σ gn = Some (Gconstant ty (Some e)).
Proof. move: Hσ Hl => /genv_compat_submodule. apply: sub_module_preserves_gconstant. Qed.

(* XXX rename/deprecate? *)
Theorem subModuleModels a b σ : b ⊧ σ -> sub_module a b -> a ⊧ σ.
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
