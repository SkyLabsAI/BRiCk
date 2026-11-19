# `tblockR` after it became a `Parameter`: open questions

[BRiCk#492](https://github.com/SkyLabsAI/BRiCk/pull/492) and [auto#705](https://github.com/SkyLabsAI/auto/pull/705)
made `tblockR` an abstract `Parameter` (`lang/cpp/logic/heap_pred/block.v`). The follow-ups
[BRiCk#493](https://github.com/SkyLabsAI/BRiCk/pull/493) and [auto#706](https://github.com/SkyLabsAI/auto/pull/706)
made element transport a lemma for class-free types, and unregistered an auto hint.
[`sizeof.md`](sizeof.md) describes which positions own `sizeof` bytes.

The full-size definition (`tblockR_raw` at every type) satisfies every axiom
(`tests/tblockR_full_size_model.v`), so the change only weakened the logic.
The questions below concern the *intended* model: a class object's storage is its data-size prefix, plus facts
that do not depend on where the object sits.

## Open

1. **Frac-valid and non-null at class types.** `tblockR_observe_frac_valid` and `tblockR_nonnull` hold at
   every type with `size_of > 0`. In the data-size model an empty class owns no bytes, so these need an
   exclusive ghost token per (address, class). [[intro.object]/10](https://eel.is/c++draft/intro.object#10)
   justifies that: two live objects share an address only if one is nested in the other, or one is a
   zero-size subobject and their types are not similar. But `wp_init_constructor` creates `tblockR` freely,
   so frac-validity relies on nothing creating two tokens at one address while one is held.
   Option: require `tblockR_raw_type ty` for both instances, if no client needs them at class types.
   **Decided 2026-11-19: leave as is.** Revisit only if a model with class-level ghost tokens turns out to be
   problematic.
2. **`tblockR_array_unfold` at class element types** places each element's abstract `tblockR` at
   `.[Tbyte ! i * sz]`. That is sound, because the stride is `sizeof` ([dcl.array]). But it constrains models,
   just as the dropped element-transport axiom did. No `wp` rule produces or consumes `tblockR` at an array type.
   Option: restrict it to `tblockR_raw_type t` and leave arrays of classes fully abstract.
3. **`implicit_destruct_tblockR_arrayR_nil_C`** (auto, `hints/layout.v`) has the same shape as
   `implicit_destruct_tblockR_arrayR_primR_C`, which auto#706 unregistered, but it is still a registered hint.
   It can fire only when a goal asks for `tblockR (Tarray ty 0)`.
4. **Lost completeness: destroy, then placement-new, of a class member.** The destructor's `tblockR (Tnamed cls)`
   no longer turns into the `blockR` that placement new wants. That is correct for base and `[[no_unique_address]]`
   subobjects. For ordinary members it waits on the data-size rule ([`sizeof.md`](sizeof.md), last section).
5. **`tblockR (Tqualified cv (Tarray t n))`** has no unfold equation. That loses completeness, not soundness.
6. **Data-size rule.** cpp2v must emit `dsize`, `nvsize` and emptiness. A type-level rule then makes
   `tblockR (Tnamed cls)` full size when they all agree with `sizeof`. First check how this overlaps with packed
   records ([BRiCk#488](https://github.com/SkyLabsAI/BRiCk/pull/488)) and virtual bases
   ([BRiCk#487](https://github.com/SkyLabsAI/BRiCk/pull/487)).
7. **Where `primR ty → tblockR_raw_type ty` lives.** auto#706 proves it in auto's `hints/layout.v`
   (`is_heap_type_tblockR_raw_type`). It is a BRiCk fact, and BRiCk's `tblockR_array_typed` could use it too.
8. **Restore `eval_o_base`?** It is commented out in `lang/cpp/semantics/ptrs.v`. It takes base offsets from
   clang's `getBaseClassOffset` and involves no sizes. It was disabled because of `implicit_destruct_struct` and
   `struct_to_raw`, which are still disabled, and `tblockR (Tnamed _)` is now abstract. All three pointer models
   prove it while ignoring the `POD \/ Standard` premise. That premise is a policy choice, as in `eval_o_field`.
   See the review on [BRiCk#497](https://github.com/SkyLabsAI/BRiCk/pull/497#discussion_r4629694044).

## Settled

- `type_ptr_array_element_tblock` relied on `sizeof` only as the array stride, which C++ guarantees.
  It was dropped as an axiom because it moved an abstract class token between byte and typed pointers, and no
  client needed that. It is now a lemma for class-free element types (BRiCk#493).
- `implicit_destruct_tblockR_arrayR_primR_C` is no longer a hint (auto#706): no rule asks for an array
  `tblockR`, and the hint also needs `type_ptr` of the whole array.
- `primR ty` implies `tblockR_raw_type ty`, so the auto lemmas need no premise for it (review on auto#706).
