(*
 * Copyright (c) 2026 BlueRock Security, Inc.
 * See the LICENSE-BedRock file in the repository root for license details.
 *)
Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.genv.
Require Import skylabs.lang.cpp.semantics.types.

Definition layout_struct : Struct :=
  Build_Struct nil nil nil nil "LayoutStruct::~LayoutStruct()"%cpp_name
    true None POD 4 4.
Definition layout_union : Union' :=
  Build_Union nil "LayoutUnion::~LayoutUnion()"%cpp_name true None 8 8.

Definition layout_tu : translation_unit :=
  Eval vm_compute in
    fst (parser.translation_unit.list_decls
      [parser.Dstruct "LayoutStruct"%cpp_name (Some layout_struct);
       parser.Dunion "LayoutUnion"%cpp_name (Some layout_union);
       parser.Denum "LayoutEnum"%cpp_name Tushort nil]
      abi.abi_default).

(** Size inference must compute name-map lookups without requiring transparent
comparison operators in typeclass conversion. *)
Section with_genv.
  Context {σ : genv} `{!genv_compat layout_tu σ}.

  Example named_struct_size : SizeOf "LayoutStruct" 4 := _.
  Example named_union_size : SizeOf "LayoutUnion" 8 := _.
  Example named_enum_size : SizeOf "LayoutEnum" 2 := _.
  Example enum_size : SizeOf (Tenum "LayoutEnum"%cpp_name) 2.
  Proof using All. apply enum_size_of. apply _. Qed.

  (** Inference can also determine the size instead of checking a supplied
  number, including underneath another [SizeOf] instance. *)
  Example inferred_named_array_size :
    exists n, SizeOf (Tarray "LayoutStruct" 3) n /\ n = 12%N.
  Proof using All. eexists. split; [apply _|reflexivity]. Qed.
End with_genv.
