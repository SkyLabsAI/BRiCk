Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.lang.cpp.semantics.genv.
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
#pragma pack(push, 4)
struct BadReference { char c; int &r; };
#pragma pack(pop)
struct __attribute__((packed)) Bytes { char c; unsigned char d; };
struct __attribute__((packed)) GoodAligned { char c; alignas(4) int i; };
struct Ordinary { int i; char c; };
struct alignas(32) Overaligned { char c; };
struct References { char c; int &r; };
template<typename T> struct __attribute__((packed)) PackedT { char c; T value; };
template struct PackedT<char>;
template struct PackedT<int>;
// Other ways to pack: the attribute on one field, the C++11 attribute
// spelling, a pragma without push (reset by an empty pragma), a member's
// alignas capped by a pragma, a packed array field, and a packed field of
// class type.
struct FieldPacked { char c; int i __attribute__((packed)); };
struct [[gnu::packed]] GnuPacked { char c; int i; };
#pragma pack(1)
struct PragmaNoPush { char c; int i; };
#pragma pack()
struct AfterReset { char c; int i; };
#pragma pack(push, 2)
struct PragmaAlignas { char c; alignas(8) long l; int i; };
#pragma pack(pop)
struct __attribute__((packed)) PackedArray { char c; short a[3]; };
struct __attribute__((packed)) PackedNested { char c; struct Inner { char d; int j; } in; };
}}.

(* Packing every record from the command line. *)
cpp.prog flag_source flags "-std=c++23 --target=x86_64-linux-gnu -fpack-struct=1" prog cpp:{{
struct FlagPacked { char c; int i; };
}}.

(** Under-aligned scalar fields get [Trealigned] types carrying the alignment
    the layout guarantees: the largest power of two dividing both the record's
    alignment and the field's offset. *)
Definition field_types (n : name) : option (list type) :=
  match source.(types) !! n with
  | Some (Gstruct s) => Some (mem_type <$> s.(s_fields))
  | Some (Gunion u) => Some (mem_type <$> u.(u_fields))
  | _ => None
  end.

Example realigned_field_layouts :
  field_types <$>
    ["BadOffset"; "BadContainer"; "BadOffsetAligned"; "BadUnion";
     "BadTypedef"; "BadPragma"; "PackedT<int>"]%cpp_name =
  [Some [Tchar; Trealigned 1 Tint]; Some [Trealigned 1 Tint];
   Some [Tchar; Trealigned 1 Tint]; Some [Trealigned 1 Tint; Tchar];
   Some [Tchar; Trealigned 1 Tint]; Some [Tchar; Trealigned 1 Tint];
   Some [Tchar; Trealigned 1 Tint]].
Proof. vm_compute. reflexivity. Qed.

Definition field_offsets (n : name) : option (list Z) :=
  match source.(types) !! n with
  | Some (Gstruct s) => Some (li_offset ∘ mem_layout <$> s.(s_fields))
  | _ => None
  end.

(* A member's own [alignas] overrides [packed]: [GoodAligned::i] sits at
   offset 4, so it keeps its natural alignment and needs no wrapper. *)
Example aligned_member_keeps_type :
  field_types "GoodAligned"%cpp_name = Some [Tchar; Tint].
Proof. vm_compute. reflexivity. Qed.

(* Offsets are in bits. *)
Example aligned_member_offset :
  field_offsets "GoodAligned"%cpp_name = Some [0; 32]%Z.
Proof. vm_compute. reflexivity. Qed.

(* The other ways to pack give the same types, since cpp2v reads Clang's
   layout rather than the attribute. Under [#pragma pack(2)], [alignas(8)]
   only reaches 2: [PragmaAlignas::l] sits at offset 2. *)
Example other_packing_syntaxes :
  field_types <$>
    ["FieldPacked"; "GnuPacked"; "PragmaNoPush"; "AfterReset";
     "PragmaAlignas"; "PackedArray"; "PackedNested::Inner"]%cpp_name =
  [Some [Tchar; Trealigned 1 Tint]; Some [Tchar; Trealigned 1 Tint];
   Some [Tchar; Trealigned 1 Tint]; Some [Tchar; Tint];
   Some [Tchar; Trealigned 2 Tlong; Trealigned 2 Tint];
   Some [Tchar; Tarray (Trealigned 1 Tshort) 3];
   Some [Tchar; Tint]].
Proof. vm_compute. reflexivity. Qed.

Example other_packing_offsets :
  field_offsets <$> ["PragmaNoPush"; "AfterReset"; "PragmaAlignas"]%cpp_name =
  [Some [0; 8]; Some [0; 32]; Some [0; 16; 80]]%Z.
Proof. vm_compute. reflexivity. Qed.

Example reject_packed_class_field :
  source.(types) !! "PackedNested"%cpp_name =
  Some (Gunsupported "under-aligned fields of class type are not supported").
Proof. vm_compute. reflexivity. Qed.

Example command_line_packing :
  (match flag_source.(types) !! "FlagPacked"%cpp_name with
   | Some (Gstruct s) => Some (mem_type <$> s.(s_fields))
   | _ => None
   end) = Some [Tchar; Trealigned 1 Tint].
Proof. vm_compute. reflexivity. Qed.

Example realigned_record_layouts :
  (fun n => (source.(types) !! n ≫= GlobDecl_size_of,
             source.(types) !! n ≫= GlobDecl_align_of)) <$>
    ["BadOffset"; "BadOffsetAligned"; "BadUnion"]%cpp_name =
  [(Some 5%N, Some 1%N); (Some 8%N, Some 4%N); (Some 4%N, Some 1%N)].
Proof. vm_compute. reflexivity. Qed.

Example reject_reference_layout :
  source.(types) !! "BadReference"%cpp_name =
  Some (Gunsupported "under-aligned reference members are not supported").
Proof. vm_compute. reflexivity. Qed.

Lemma align_of_realigned_int {σ : genv} : align_of (Trealigned 1 Tint) = Some 1%N.
Proof. by apply: (align_of_realigned _ _ 4). Qed.

(* [Trealigned] can also over-align: [int] has size 4, yet can sit at 32. *)
Lemma align_of_realigned_overaligned_int {σ : genv} :
  align_of (Trealigned 32 Tint) = Some 32%N.
Proof. by apply: (align_of_realigned _ _ 4). Qed.

(* Clang rejects arrays whose element size is not a multiple of the element
   alignment, so such arrays have no size (even under qualifiers). *)
Example overaligned_array_has_no_size {σ : genv} :
  size_of σ (Tarray (Trealigned 32 Tint) 2) = None.
Proof. reflexivity. Qed.
Example qualified_overaligned_array_has_no_size {σ : genv} :
  size_of σ (Tarray (Tconst (Trealigned 32 Tint)) 2) = None.
Proof. reflexivity. Qed.
Example underaligned_array_size {σ : genv} :
  size_of σ (Tarray (Trealigned 1 Tint) 2) = Some 8%N.
Proof. reflexivity. Qed.
(* A single over-aligned object keeps its size. *)
Example overaligned_size {σ : genv} : size_of σ (Trealigned 32 Tint) = Some 4%N.
Proof. reflexivity. Qed.

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

(* [RealignOk] is found by instance search on concrete types, and fails
   quickly on an abstract one. *)
Section realign_ok_instances.
  Context {σ : genv}.
  Example realign_ok_named : @RealignOk σ "Ordinary"%cpp_type := _.
  Example realign_ok_ptr : @RealignOk σ (Tptr (Trealigned 32 Tint)) := _.
  Example realign_ok_qualified : @RealignOk σ (Tconst "Ordinary"%cpp_type) := _.
  Example realign_ok_array : @RealignOk σ (Tarray Tint 3) := _.
  Example realign_ok_array_named : @RealignOk σ (Tarray "Ordinary"%cpp_type 3) := _.
  Example realign_ok_underaligned : @RealignOk σ (Tarray (Trealigned 1 Tint) 3) := _.
  Example realign_ok_erase : @RealignOk σ (erase_qualifiers (Tconst (Tarray Tint 2))) := _.
  Example realign_ok_overaligned_scalar_fails :
    @RealignOk σ (Trealigned 32 Tint) -> False.
  Proof.
    intros H. have := H 4%N eq_refl. vm_compute. done.
  Qed.
  Example realign_ok_abstract_fails (ty : type) : True.
  Proof. Fail Timeout 5 assert (@RealignOk σ ty) by apply _. done. Qed.
End realign_ok_instances.
