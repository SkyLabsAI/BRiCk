(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.syntax.typed.
Require Import skylabs.lang.cpp.semantics.genv.
Require Import skylabs.lang.cpp.semantics.types.

Set Default Proof Using "Type*".
Set Default Goal Selector "!".

(** Pure AST regressions: no cpp2v invocation or separation-logic imports. *)
#[local] Definition metadata : OpaqueRecord :=
  Build_OpaqueRecord "Opaque::~Opaque()"%cpp_name false 16 8.

#[local] Definition source : translation_unit :=
  Eval vm_compute in
    fst (parser.translation_unit.list_decls
      [parser.Dtype "Opaque"%cpp_name;
       parser.Dopaque_record "Opaque"%cpp_name metadata]
      abi.x64_linux).

#[local] Definition environment : genv :=
  {| genv_tu := source; member_pointer_bitsize := bitsize.W64 |}.

Example opaque_record_lookup :
  source.(types) !! "Opaque"%cpp_name = Some (Gopaque_record metadata).
Proof. vm_compute. reflexivity. Qed.

Example opaque_record_size :
  size_of environment "Opaque"%cpp_type = Some 16%N.
Proof. vm_compute. reflexivity. Qed.

Example opaque_record_alignment_metadata :
  (source.(types) !! "Opaque"%cpp_name >>= GlobDecl_align_of,
   source.(types) !! "Opaque"%cpp_name >>= GlobDecl_valid_align_of) =
  (Some 8%N, Some 8%N).
Proof. vm_compute. reflexivity. Qed.

Example opaque_record_linked_metadata (σ : genv) (Hσ : source ⊧ σ) :
  glob_def σ "Opaque"%cpp_name = Some (Gopaque_record metadata).
Proof. exact (glob_def_genv_compat_opaque_record metadata opaque_record_lookup). Qed.

Example opaque_record_linked_size (σ : genv) (Hσ : source ⊧ σ) :
  glob_def σ "Opaque"%cpp_name >>= GlobDecl_size_of = Some 16%N.
Proof.
  apply (glob_def_genv_compat_size (tu := source)).
  vm_compute. reflexivity.
Qed.

Example opaque_record_linked_alignment (σ : genv) (Hσ : source ⊧ σ) :
  glob_def σ "Opaque"%cpp_name >>= GlobDecl_valid_align_of = Some 8%N.
Proof.
  apply (glob_def_genv_compat_valid_align (tu := source)).
  vm_compute. reflexivity.
Qed.

Example opaque_record_invalid_alignment :
  GlobDecl_valid_align_of
    (Gopaque_record (Build_OpaqueRecord "Opaque::~Opaque()"%cpp_name false 16 3)) = None.
Proof. vm_compute. reflexivity. Qed.

Example opaque_record_complete_decl :
  complete_decl source.(types) (Gopaque_record metadata).
Proof. apply complete_opaque_record. Qed.

Example opaque_record_complete_type :
  complete_type source.(types) "Opaque"%cpp_type.
Proof.
  eapply complete_named with (decl := Gopaque_record metadata).
  { apply opaque_record_lookup. }
  apply complete_opaque_record.
Qed.

Example opaque_record_compatibility_is_exact (r r' : OpaqueRecord) :
  GlobDecl_le (Gopaque_record r) (Gopaque_record r') = bool_decide (r = r').
Proof. reflexivity. Qed.

Example opaque_record_compatible_with_itself :
  GlobDecl_le (Gopaque_record metadata) (Gopaque_record metadata) = true.
Proof. vm_compute. reflexivity. Qed.

(* Each metadata field is independently significant for compatibility. *)
Example opaque_record_rejects_metadata_changes :
  (fun r => GlobDecl_le (Gopaque_record metadata) (Gopaque_record r)) <$>
    [Build_OpaqueRecord "Other::~Other()"%cpp_name false 16 8;
     Build_OpaqueRecord "Opaque::~Opaque()"%cpp_name true 16 8;
     Build_OpaqueRecord "Opaque::~Opaque()"%cpp_name false 24 8;
     Build_OpaqueRecord "Opaque::~Opaque()"%cpp_name false 16 16] =
  [false; false; false; false].
Proof. vm_compute. reflexivity. Qed.

Example opaque_record_refines_forward_declaration :
  (GlobDecl_le Gtype (Gopaque_record metadata),
   GlobDecl_le (Gopaque_record metadata) Gtype) = (true, false).
Proof. reflexivity. Qed.

Example opaque_record_does_not_refine_visible_struct (s : Struct) :
  (GlobDecl_le (Gopaque_record metadata) (Gstruct s),
   GlobDecl_le (Gstruct s) (Gopaque_record metadata)) = (false, false).
Proof. reflexivity. Qed.

Example opaque_record_does_not_refine_visible_union (u : decl.Union) :
  (GlobDecl_le (Gopaque_record metadata) (Gunion u),
   GlobDecl_le (Gunion u) (Gopaque_record metadata)) = (false, false).
Proof. reflexivity. Qed.

Example opaque_record_has_no_field_offsets (fld : atomic_name) :
  offset_of environment "Opaque"%cpp_name fld = None.
Proof. vm_compute. reflexivity. Qed.

Example opaque_record_has_no_base_offsets (base : name) :
  parent_offset_tu source "Opaque"%cpp_name base = None.
Proof. vm_compute. reflexivity. Qed.

Example opaque_record_field_type_unavailable :
  trace.runO (typed.decltype.of_expr source
    (Eglobal "Opaque::hidden"%cpp_name "int"%cpp_type)) = None.
Proof. vm_compute. reflexivity. Qed.
