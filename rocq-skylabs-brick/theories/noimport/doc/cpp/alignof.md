# Where `alignof` describes an object's address

`alignof(T)` is a property of the *type*, measured on complete objects. A base class subobject
can be less aligned than `alignof` of its class when the class has virtual bases. This is the
alignment counterpart of [`sizeof.md`](sizeof.md).

## The rule

[[basic.align]/2](https://eel.is/c++draft/basic.align#2): "The alignment required for a type may
be different when it is used as the type of a complete object and when it is used as the type of
a subobject." And "the result of the `alignof` operator reflects the alignment requirement of the
type in the complete-object case." The standard's example:

```cpp
struct B { long double d; };
struct D : virtual B { char c; };
```

"When D is the type of a complete object, it will have a subobject of type B, so it must be
aligned appropriately for a long double." As a subobject of an object that also has `B` as a
virtual base, the `B` subobject may be elsewhere, "reducing the alignment requirements on the D
subobject."

## Itanium ABI

The ABI places a base class subobject, virtual or not, at an offset aligned to its **non-virtual
alignment** (`nvalign`, clang `ASTRecordLayout::getNonVirtualAlignment`), which leaves out the
virtual bases. For a class without virtual bases, `nvalign == alignof`. A class with a virtual base
more aligned than the rest of the class has `nvalign < alignof`.

```cpp
struct alignas(16) V { char v; };
struct C : virtual V { };   // alignof(C) == 16, nvalign(C) == 8
struct P : virtual V { };
struct D : P, C { };        // C at offset 8, V at offset 16
```

Here a complete `D` is 16-aligned and its `C` subobject is at an address that is 8 modulo 16
(clang 22, x86-64, at `-O0` and `-O2`).

## What BRiCk relies on

- `align_of (Tnamed cls)` is the complete-object alignment, `s_alignment` (`GlobDecl_align_of`,
  `semantics/types.v`), also for a class with virtual bases (`Gvstruct`). This is right for `alignof`
  (`wp_operand_alignof`) and for allocating complete objects.
- Every *pointer* of class type is assumed aligned to it as well: `aligned_ptr_ty` uses `align_of`,
  `has_type (Vptr p) (Tptr ty)` implies `aligned_ptr_ty ty p` (`has_type_ptr'`), and so do
  `reference_to` and `type_ptr`. `wp_operand_well_typed` gives `has_type` for every operand, e.g.
  `this` in a constructor of `C`, and the constructor rules give `reference_toR (Tnamed cls)` at
  `this` (`svalid_members`, `logic/func.v`).

So BRiCk assumes that every object of class type is aligned to `alignof` of its class. C++ does not
guarantee that for base subobjects of classes with virtual bases, as in `D` above, where the logic
proves that `(unsigned long)this % 16 == 0` in `C::C()`, while the program sees 8.

## Why this is not reachable today

cpp2v emits a class as `Gunsupported "under-aligned base classes are not supported"` when one of
its bases, virtual or not, sits at an offset not aligned to the base's full alignment
(`supportedCXXRecord`, `rocq-skylabs-cpp2v/src/PrintDecl.cpp`). `D` above is rejected, so no
supported class constructs a `C` base subobject below 16-byte alignment. The checks compose: a
supported class's alignment is a multiple of each base's alignment, so a base of a base is aligned
too. The conditional witness
[`vbase_alignment`](https://github.com/SkyLabsAI/auto/tree/main/rocq-skylabs-auto-cpp/tests/unsound/conditional/vbase_alignment)
in auto proves that `C::C()` never returns, and checks that cpp2v rejects `D`.

The logic's own layout check is weaker than cpp2v's: for a virtual base that has virtual bases
itself, `vbase_req` (`logic/vstruct_layout.v`) requires only `vs_nv_alignment`. That matters only
for translation units that do not come from cpp2v.

## What would let such classes be supported

`align_of` would need to split into two notions:

1. the complete-object alignment, for `alignof` and for allocation;
2. the alignment that every object of the type has, which is `vs_nv_alignment` for a class with
   virtual bases, for `aligned_ptr_ty` and so for `has_type`, `reference_to` and `type_ptr`.

Only then could cpp2v accept bases at their non-virtual alignment.
