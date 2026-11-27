# Where `sizeof` describes an object's storage

`sizeof(T)` is a property of the *type*. Whether an object of type `T` owns `sizeof(T)` bytes
depends on *where the object sits*. Only potentially-overlapping subobjects can own fewer.

## The rule

An object owns `sizeof(T)` bytes, tail padding included, unless it is a
**potentially-overlapping subobject**
([[intro.object]/7](https://eel.is/c++draft/intro.object#7)): a base class subobject, or a
non-static data member declared `[[no_unique_address]]`.

| Position | Owns `sizeof(T)` bytes? | Why |
|---|---|---|
| Complete object (variable, `new`, temporary) | yes | its storage is allocated for `sizeof(T)` bytes |
| Array element | yes | elements are contiguous and `sizeof(T[n]) == n * sizeof(T)` ([dcl.array], [expr.sizeof]/2); never potentially overlapping |
| Ordinary non-static data member | yes | not potentially overlapping, so it occupies `sizeof(T)` bytes that no other member of the enclosing object uses |
| `[[no_unique_address]]` member | **no** | may share its tail padding with later members, or take no bytes if it is empty |
| Base class subobject | **no** | may share its tail padding, take no bytes if empty (empty-base optimization), and excludes its virtual bases |

`[[no_unique_address]]` members behave like bases here, not like other fields.

Normative anchors (current working draft):
- [[expr.sizeof]/1](https://eel.is/c++draft/expr.sizeof#1): `sizeof` yields "the number of bytes
  occupied by a non-potentially-overlapping object of the type of its operand". This is the rule
  itself.
- [[expr.sizeof]/2](https://eel.is/c++draft/expr.sizeof#2): for a class, `sizeof` includes the padding needed
  to place objects of that type in an array. Applied to a potentially-overlapping subobject, it gives
  the size of the type, not the size of the subobject. An array of `n` elements has `n` times the size of an element.
- [[basic.types.general]/2](https://eel.is/c++draft/basic.types.general#2): the object representation of a type
  `T` is the `sizeof(T)` bytes taken up by a non-bit-field *complete* object of type `T`.
- [[basic.types.trivial]/3](https://eel.is/c++draft/basic.types.trivial#3): the underlying bytes of a trivially
  copyable object can be copied out and back only if it "is not a potentially-overlapping subobject".
- [[intro.object]/8](https://eel.is/c++draft/intro.object#8): only a potentially-overlapping subobject of class
  type can have zero size. An object of nonzero size occupies one or more bytes.
- [[intro.object]/10](https://eel.is/c++draft/intro.object#10): two non-bit-field objects with overlapping
  lifetimes occupy disjoint bytes, unless one is nested within the other, at least one is a subobject of zero
  size and their types are not similar, or both are potentially non-unique objects (such as string literals).

## How much a potentially-overlapping subobject owns (Itanium ABI)

- **Data size** (`dsize`, clang `ASTRecordLayout::getDataSize`) is the size without tail padding.
  After a potentially-overlapping subobject, the ABI may place the next field or base at offset `dsize`,
  not at `sizeof`. Exception: when the class is "POD for the purpose of layout", which is C++03 POD,
  `dsize == sizeof`. C++03 POD is not `std::is_pod`. A class with private data members, or with an empty
  base, can satisfy `std::is_pod` and still have its tail padding reused.
- **Empty classes** have `sizeof >= 1`. As potentially-overlapping subobjects they can occupy zero bytes,
  sharing an address with a subobject of a *different* type. clang reports `dsize == 1` for an empty
  struct, so `dsize == sizeof` does not by itself mean that the class owns its byte.
- **Virtual bases**: `sizeof(B)` counts the virtual bases of `B`, but a `B` base subobject does not contain them.
  It owns at most the non-virtual size (`nvsize`, clang `getNonVirtualSize`).

So a class owns `sizeof` bytes at *every* position only when `dsize == sizeof`, the class is not empty,
and, if it has virtual bases, `nvsize == sizeof`. cpp2v emits none of these facts today. It records only
`s_size` (clang `getSize()`).

## What BRiCk relies on

Trusted, and justified by the table above:
- `o_sub σ ty i` is displaced by `i * size_of σ ty` (`semantics/ptrs.v`). This is the array stride,
  which C++ guarantees for every element type, classes included.
- `size_of` as the allocation size of complete objects (`new`, locals, temporaries).
- `tblockR ty q` (`logic/heap_pred/block.v`) is `size_of σ ty` bytes (`tblockR_raw_eq`) only when
  `tblockR_raw_type ty`, which holds when `ty` contains no class type, looking through arrays and
  qualifiers (`class_free_type`, `semantics/types.v`). An object of class-free type is never a base
  subobject, and the ABI does not reuse its tail even as a `[[no_unique_address]]` member.
- `type_ptr_obj_repr_byte` (`logic/pred.v`) gives `type_ptr Tbyte (p .[Tbyte ! i])` for each
  `i < size_of σ ty` only when `class_free_type ty`. So do the lemmas built on it
  (`type_ptr_obj_repr`, `type_ptr_raw_type_ptrs`, `type_ptr_byte_end`, the `blockR` transports in
  `logic/object_repr.v`). At a class type it would claim bytes the object may not own, e.g. past the
  end of the complete object: with clang 22 on x86-64,
  `struct E {}; struct F {}; struct X : E {}; struct C : X, virtual E { long c; };`
  `struct P : virtual F { long p; }; struct D : P, C {};` places the `C` base of a 32-byte `D` at
  offset 16, and `sizeof(C) == 24` would reach byte 39.

Deliberately not trusted:
- `tblockR (Tnamed cls)` is abstract and unrelated to `size_of σ (Tnamed cls)` ([BRiCk#492](https://github.com/SkyLabsAI/BRiCk/pull/492)).
  Destructors return it for *every* class object, base subobjects and `[[no_unique_address]]` members
  included, so it cannot claim `sizeof` bytes. Regression test:
  [`base_tail_padding`](https://github.com/SkyLabsAI/auto/tree/main/rocq-skylabs-auto-cpp/tests/unsound/fixed_regression_tests/base_tail_padding)
  in auto.
- `struct_to_raw`, which views a whole class object as bytes, is disabled (`logic/layout.v`, see
  [BRiCk#310](https://github.com/SkyLabsAI/BRiCk/issues/310)).
- `eval_o_base` is commented out (`semantics/ptrs.v`) because it conflicts with the disabled
  `implicit_destruct_struct` and `struct_to_raw`, which let a base claim `sizeof` bytes. It does not
  depend on sizes itself: base offsets come from clang (`getBaseClassOffset`), and `o_base` is not
  used for virtual bases.

## What would let class objects be bytes again

1. cpp2v emits `dsize`, `nvsize` and emptiness for each class (clang `getDataSize`, `getNonVirtualSize`,
   `CXXRecordDecl::isEmpty`).
2. A type-level rule: when `dsize == nvsize == sizeof` and the class is not empty,
   `tblockR (Tnamed cls)` is `blockR sizeof ** alignedR` at every position, and
   `type_ptr_obj_repr_byte` holds at `Tnamed cls`.
3. Optionally, evidence of an object's position (complete object, array element or ordinary member).
   With it, other classes own `sizeof` bytes wherever they are not potentially overlapping.
