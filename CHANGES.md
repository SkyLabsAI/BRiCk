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
- New **abstract** representation predicate `initializer_listR ety q arrayp n`
  in `lang/cpp/logic/expr.v`. This is what specifications of
  `std::initializer_list` should be written against. Its interface is the global
  instances `initializer_listR_cfractional`, `initializer_listR_type_ptr` and
  `initializer_listR_agree`, plus the derived `initializer_listR_ascfractional`.
  Destruction is *not* part of it: that goes through the standard library's
  destructor specification, which consumes the predicate directly.

  It is abstract because `std::initializer_list` has no specified data members,
  so every conforming representation is isomorphic to the (base pointer, element
  count) pair the predicate carries. The rationale is stated in full at
  `initializer_listR`; it is not repeated elsewhere.

  `ety` is the class's **template argument**, not the backing array's element
  type — <http://eel.is/c++draft/dcl.init.list#5> makes the array `const ety[n]`,
  so the two differ by that `const`. See `std_initializer_list_element` in
  `lang/cpp/syntax/types.v`.
- New `Tstd_initializer_list ety` abbreviation and
  `std_initializer_list_element` in `lang/cpp/syntax/types.v`, alongside the
  existing `std_initializer_list` name.
- `wp_init_initlist_std` grants `initializer_listR` for the backing array it
  evaluates. It requires the class to be `std::initializer_list<E>` and the
  backing array to be `const E[N]` for that same `E`.
  `lang/cpp/syntax/typed.v` checks a weaker condition — it does not require a
  known extent — so `cpp2v --check-types` rejects malformed nodes but accepting
  a node does not by itself mean the rule applies to it.
- The lifetime-extended case, e.g. `std::initializer_list<int> il = {1,2,3};`,
  is still unsupported because it requires scope-extruded temporaries.

2025.03.20: Change global prefix `bedrock.xxx` to `bluerock.xxx`
- See `scripts/fm-refactorings/bedrock-bluerock.sh`

2025.03.17: Split the C++ program logic BRiCk from the BlueRock prelude (`rocq-skylabs-prelude`) and Iris extensions (`rocq-skylabs-iris`).
- See `scripts/fm-refactorings/split-brick.sh`


