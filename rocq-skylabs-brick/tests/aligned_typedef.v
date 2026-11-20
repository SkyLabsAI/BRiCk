(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.lang.cpp.semantics.types.
Require Import skylabs.lang.cpp.semantics.sub_module.

(** * Alignment attributes on typedefs

    cpp2v erases a typedef to its underlying type, losing an alignment
    attribute. Two places observe that attribute, and cpp2v handles both:
    - <<alignof>> of the typedef, which cpp2v prints as the constant Clang
      computes, since BRiCk models <<alignof(T)>> by [align_of] of the erased
      type;
    - a field whose offset the attribute lowers below the alignment of the
      erased type, which cpp2v prints with a [Trealigned] type.
    The static assertions state what Clang computes. *)

cpp.prog source flags "-std=c++17 --target=x86_64-linux-gnu" prog cpp:{{
typedef int X __attribute__((aligned(16)));
typedef unsigned short u16a __attribute__((aligned(1)));
static_assert(sizeof(X) == 4 && alignof(X) == 16, "over-aligned typedef");
static_assert(sizeof(u16a) == 2 && alignof(u16a) == 1, "under-aligned typedef");
unsigned long a_over() { return alignof(X); }
unsigned long a_under() { return alignof(u16a); }
unsigned long a_plain() { return alignof(int); }
struct Over { char c; X x; };
static_assert(sizeof(Over) == 32 && alignof(Over) == 16, "over-aligned field");
struct Under { char c; u16a u; };
static_assert(sizeof(Under) == 3 && alignof(Under) == 1, "under-aligned field");
}}.

Example typedefs_lose_alignment :
  (fun n => source.(types) !! n) <$> ["X"; "u16a"]%cpp_name =
  [Some (Gtypedef Tint); Some (Gtypedef Tushort)].
Proof. vm_compute. reflexivity. Qed.

Definition returned (tu : translation_unit) (n : name) : option Expr :=
  match tu.(symbols) !! n with
  | Some (Ofunction f) =>
      match f.(f_body) with
      | Some (Impl (Sseq [Sreturn (Some e)])) => Some e
      | _ => None
      end
  | _ => None
  end.

(** <<alignof>> of an attributed typedef is Clang's constant; other
    <<alignof>> expressions are unchanged. *)
Example alignof_attributed_is_constant :
  returned source <$> ["a_over()"; "a_under()"; "a_plain()"]%cpp_name =
  [Some (Eint 16 Tulong); Some (Eint 1 Tulong); Some (Ealignof (inl Tint) Tulong)].
Proof. vm_compute. reflexivity. Qed.

(** An over-aligned field only raises the record's alignment. *)
Example over_aligned_field_layout :
  (source.(types) !! "Over"%cpp_name ≫= GlobDecl_size_of,
   source.(types) !! "Over"%cpp_name ≫= GlobDecl_align_of) =
  (Some 32%N, Some 16%N).
Proof. vm_compute. reflexivity. Qed.

(** An under-aligned field gets a [Trealigned] type. *)
Example under_aligned_field_realigned :
  match source.(types) !! "Under"%cpp_name with
  | Some (Gstruct s) => Some (mem_type <$> s.(s_fields), s.(s_size), s.(s_alignment))
  | _ => None
  end = Some ([Tchar; Trealigned 1 Tushort], 3%N, 1%N).
Proof. vm_compute. reflexivity. Qed.

(** A variable declared at the erased type in one translation unit cannot be
    linked with an under-aligned definition in another: their symbols are
    incompatible, so no single [genv] models both units. *)
Example extern_realigned_incompatible :
  ObjValue_le (Ovar Tushort global_init.Extern)
              (Ovar (Trealigned 1 Tushort) global_init.NoInit) = false.
Proof. vm_compute. reflexivity. Qed.
