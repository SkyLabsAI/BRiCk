# Changelog

### How to use

This document is a best-effort that tracks breaking changes to the code base.

When adding a new entry, add it to the **top** of the list with the date.
When a release occurs, change the `Since Last Release` heading to the name
of the release, and introduce a new heading.

## Since Last Release

2026.10.29: C++ name/type notation now parses and prints array declarators
with C++ precedence and dimension order ([#448](https://github.com/SkyLabsAI/BRiCk/issues/448),
[#453](https://github.com/SkyLabsAI/BRiCk/pull/453)).
- Array references use `int(&)[3]`; the malformed `int[3]&` spelling is rejected.
  Update affected `%cpp_name` and `%cpp_type` literals to the valid spelling.
- Multidimensional arrays use outermost-first dimensions: `int[5][10]` means
  five arrays of ten integers. Literals that relied on the previous reversed
  order must reverse their dimensions to preserve their intended type; for
  example, two zero-length byte arrays are now `unsigned char[2][0]`.

2026.10.19: cpp2v puts template patterns reached outside their template (e.g.
local types in out-of-line member definitions of class templates, or
out-of-line static data members of class templates) in the template part of
the AST instead of the static one. The static part of a translation unit no
longer depends on `--no-templates`, so units generated with and without
templates are `sub_module`s of each other.

2026.10.13: `Egnu_null t` (GNU `__null`, i.e. `NULL` in GNU C++) is now
`Eint 0 t` instead of `Ecast (Cptr2int t) Enull`, which had no semantics, so
every use of `NULL` was unprovable.

2026.07.29: Add support for clang's `CXXStdInitializerListExpr`, i.e. the
implicit construction of a `std::initializer_list<E>` from a braced-init-list
(<http://eel.is/c++draft/dcl.init.list#5>).
- New `Expr` constructor `Einitlist_std (backing : Expr) (t : type)`. Downstream
  exhaustive matches over `Expr` need a new case.
- `wp_init_initlist_std` reduces it to the `std::initializer_list` constructor
  named by `std_initlist_ctor` (`lang/cpp/syntax/types.v`), following
  `wp_init_binop_spaceship`. The representation of the resulting object belongs
  to whoever specifies that constructor; see `brick-libcpp`.
- The lifetime-extended case, e.g. `std::initializer_list<int> il = {1,2,3};`,
  is still unsupported because it requires scope-extruded temporaries.

2025.03.20: Change global prefix `bedrock.xxx` to `bluerock.xxx`
- See `scripts/fm-refactorings/bedrock-bluerock.sh`

2025.03.17: Split the C++ program logic BRiCk from the BlueRock prelude (`rocq-skylabs-prelude`) and Iris extensions (`rocq-skylabs-iris`).
- See `scripts/fm-refactorings/split-brick.sh`


