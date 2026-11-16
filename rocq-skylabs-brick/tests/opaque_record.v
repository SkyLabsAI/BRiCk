(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Import skylabs.iris.extra.bi.errors.
Require Import skylabs.lang.cpp.logic.
Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.lang.cpp.syntax.supported.

(** * Opaque records (SkyLabsAI/BRiCk#307)

    cpp2v cannot model the body of a record with bit-fields. Rather than
    [Gunsupported], which has no size and is not a complete type, it
    emits a [Gopaque] carrying the record's size, alignment,
    destructor, and <<operator delete>>. Callers can then own such an object
    through an abstract [Rep], pass it by value, and destroy it; its members
    stay out of reach. *)

cpp.prog source flags "-std=c++20 --target=x86_64-linux-gnu" prog cpp:{{
  class Bits {
    unsigned long block_ : 40;
    unsigned long tx_ : 24;
  public:
    bool operator==(Bits that) const;
  };
  struct HasBits { int x; Bits b; };
  bool same(Bits a, Bits b) { return a == b; }
}}.

Definition Bits_opaque : Opaque :=
  {| o_size := 8
   ; o_alignment := 8
   ; o_dtor := "Bits::~Bits()"
   ; o_trivially_destructible := true
   ; o_delete := None
   ; o_reason := "bitfields are not supported"
   ; o_bitfields := [] |}.

Example opaque_record_entry :
  source.(types) !! "Bits"%cpp_name = Some (Gopaque Bits_opaque).
Proof. vm_compute. reflexivity. Qed.

(** ** What an opaque record provides *)

(** The policy of [supported.v]: the translation unit is usable. *)
Example opaque_record_supported : check.translation_unit source = [].
Proof. vm_compute. reflexivity. Qed.

(** The C++ type is complete, so it can be passed by value. *)
Example opaque_record_complete : complete_type source.(types) "Bits".
Proof. by econstructor; [exact: opaque_record_entry|constructor]. Qed.

Example opaque_record_callable :
  callable_type source.(types) "bool (Bits, Bits)".
Proof.
  split; first by repeat constructor.
  do 2 (constructor; first exact: opaque_record_complete). constructor.
Qed.

Example opaque_record_trivially_destructible :
  is_trivially_destructible source "Bits" = true.
Proof. vm_compute. reflexivity. Qed.

(** An enclosing record is an ordinary struct, laid out around the opaque
    member. *)
Example opaque_member_enclosing_size :
  (source.(types) !! "HasBits"%cpp_name) ≫= GlobDecl_size_of = Some 16%N.
Proof. vm_compute. reflexivity. Qed.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv} {MODd : source ⊧ CU}.

  (** Every compatible runtime environment keeps the same metadata. *)
  Lemma runtime_record_entry :
    glob_def CU "Bits" = Some (Gopaque Bits_opaque).
  Proof using MODd. exact: glob_def_genv_compat_opaque opaque_record_entry. Qed.

  Lemma runtime_record_size : size_of CU "Bits" = Some 8%N.
  Proof using MODd. by rewrite /= runtime_record_entry. Qed.

  Lemma runtime_record_align : align_of "Bits" = Some 8%N.
  Proof using MODd.
    by rewrite (align_of_genv_compat_opaque source _ _ MODd opaque_record_entry).
  Qed.

  (** The type has a size, so [type_ptr "Bits" p] would stay consistent
      even with the former axiom [type_ptr_size]. *)
  Lemma opaque_record_has_size : is_Some (size_of CU "Bits").
  Proof using MODd. by rewrite runtime_record_size. Qed.

  (** Destruction calls the recorded destructor, via its specification. *)
  Lemma opaque_record_destroy (p : ptr) (Q : epred) :
    wp_destroy_named source "Bits" p Q -|-
    wp_destructor source "Bits" (_global "Bits::~Bits()") p Q.
  Proof using.
    split'.
    - exact: wp_destroy_named_elim_opaque opaque_record_entry.
    - exact: wp_destroy_named_intro_opaque opaque_record_entry.
  Qed.

  (** ** What an opaque record withholds *)

  (** No member has an offset, so no member can be accessed. *)
  Lemma opaque_record_no_offset (f : atomic_name) : offset_of CU "Bits" f = None.
  Proof using MODd. by rewrite /offset_of runtime_record_entry. Qed.
End with_Sigma.

(** The body is needed to change <<const>>-ness and to select a destructor
    for <<delete>>; both stay unsupported. An opaque record is also not
    compatible with a struct carrying the same metadata (see [GlobDecl_le]). *)
Example opaque_record_not_below_struct :
  GlobDecl_le (Gopaque Bits_opaque)
    (Gstruct (Build_Struct [] [] [] [] "Bits::~Bits()" true None POD 8 8)) = false.
Proof. reflexivity. Qed.
