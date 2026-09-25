Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.lang.cpp.semantics.types.

Set Default Proof Using "Type*".

cpp.prog source flags "-std=c++23 --target=x86_64-linux-gnu" prog cpp:{{
struct __attribute__((packed)) BadOffset { char c; int i; };
struct __attribute__((packed)) BadContainer { int i; };
struct __attribute__((packed, aligned(4))) BadOffsetAligned { char c; int i; };
union __attribute__((packed)) BadUnion { int i; char c; };
typedef int LowInt __attribute__((aligned(1)));
struct BadTypedef { char c; LowInt i; };
struct Base { int i; };
typedef Base LowBase __attribute__((aligned(1)));
#pragma pack(push, 1)
struct BadPragma { char c; int i; };
struct BadDerived : Base { char c; };
struct BadDerivedTypedef : LowBase { char c; };
#pragma pack(pop)
struct __attribute__((packed)) Bytes { char c; unsigned char d; };
struct __attribute__((packed)) GoodAligned { char c; alignas(4) int i; };
struct Ordinary { int i; char c; };
struct alignas(32) Overaligned { char c; };
struct References { char c; int &r; };
template<typename T> struct __attribute__((packed)) PackedT { char c; T value; };
template struct PackedT<char>;
template struct PackedT<int>;
}}.

Example reject_field_layouts :
  (fun n => source.(types) !! n) <$>
    ["BadOffset"; "BadContainer"; "BadOffsetAligned"; "BadUnion";
     "BadTypedef"; "BadPragma"; "PackedT<int>"]%cpp_name =
  replicate 7 (Some (Gunsupported "under-aligned fields are not supported")).
Proof. vm_compute. reflexivity. Qed.

Example reject_base_layout :
  (fun n => source.(types) !! n) <$>
    ["BadDerived"; "BadDerivedTypedef"]%cpp_name =
  replicate 2 (Some (Gunsupported "under-aligned base classes are not supported")).
Proof. vm_compute. reflexivity. Qed.

Example supported_layouts_keep_alignment :
  (fun n => source.(types) !! n ≫= GlobDecl_align_of) <$>
    ["Bytes"; "GoodAligned"; "Ordinary"; "Overaligned"; "References";
     "PackedT<char>"]%cpp_name =
  [Some 1%N; Some 4%N; Some 4%N; Some 32%N; Some 8%N; Some 1%N].
Proof. vm_compute. reflexivity. Qed.

(* Reference cells keep pointer layout even when the referent is an int. *)
Example reference_storage_size :
  source.(types) !! "References"%cpp_name ≫= GlobDecl_size_of = Some 16%N.
Proof. vm_compute. reflexivity. Qed.
