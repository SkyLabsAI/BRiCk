# Changelog

### How to use

This document is a best-effort that tracks breaking changes to the code base.

When adding a new entry, add it to the **top** of the list with the date.
When a release occurs, change the `Since Last Release` heading to the name
of the release, and introduce a new heading.

## Since Last Release

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


