# Changelog

### How to use

This document is a best-effort that tracks breaking changes to the code base.

When adding a new entry, add it to the **top** of the list with the date.
When a release occurs, change the `Since Last Release` heading to the name
of the release, and introduce a new heading.

## Since Last Release

2026.11.25: cpp2v keeps `[[clang::trivial_abi]]` classes with bit-fields
`Dunsupported`, instead of exposing them as opaque records. Their argument
lifetime is unsupported even when their field layout is hidden.

2026.11.24: `global_ptr_nonnull`, `global_ptr_nonnull_aid` and
`global_ptr_nonnull_addr` (and `_global_nonnull`) now require
`defines_symbol tu o = true`: the translation unit defines the symbol, rather
than only declaring it. An undefined weak symbol is at address 0. The new
`_global_nonnull_defined` takes the definition from a `tu ⊧ σ`, by
`sub_module_defines_symbol`.

2026.11.24: cpp2v prints three constructs whose attributes BRiCk does not
model as unsupported, instead of dropping the attribute: a statement that
declares a local variable with `__attribute__((cleanup(f)))` is
`Sunsupported`; a reference to a `weak`, `weakref` or `weak_import` variable
or function that the translation unit does not define is `Eunsupported` (the
linker may resolve it to address 0, while `global_ptr_nonnull` makes every
global non-null); and a `[[clang::trivial_abi]]` class is `Dunsupported`
(its callee destroys by-value parameters). Proofs about such code no longer
go through.

2026.11.24: `VarDecl` has a new constructor `Dvla_bounds (bounds : list Expr)`:
a declaration of a variably modified type (GNU variable-length arrays in C++)
that declares no object. It evaluates the array bounds in order, and each must
be greater than zero (`wp_vla_bounds` in `logic/stmt.v`). cpp2v prints it for
a typedef or alias declaration of such a type (`typedef int A[n];`) and, as
the first statement of the body, for the parameters of a function
(`int f(int n, int a[n])`); it used to drop these bounds. Code that matches on
`VarDecl` needs a case, and proofs of such functions get the obligation
`0 < n` for each bound. The declaration of a local variable of such a type
(`int (*p)[n];`) is preceded by a `Dvla_bounds` in its `Sdecl`. A condition
variable of, and an explicit cast to, a variably modified type whose bounds
are evaluated there are printed as unsupported. Variable-length arrays
themselves (`int a[n];`) are printed as before.

2026.11.24: cpp2v prints C++ assumptions as unsupported: `[[assume(e)]];`
(also `__attribute__((assume(e)));`) as `Sunsupported`, and `__builtin_assume(e)`
as `Eunsupported`. The attribute forms used to print as `Sattr ["assume"] Sskip`,
which the logic skips, although a false assumption is undefined behaviour.
Proofs about such code, which were unsound, no longer go through. More
generally, a statement prints as `Sattr` only when all its attributes are
hints or diagnostics (`likely`, `fallthrough`, loop hints, ...); any other
statement attribute makes the statement `Sunsupported`. That includes
`#pragma clang loop vectorize(assume_safety)` and `[[clang::musttail]]`
(`__attribute__((musttail))`), which ends the lifetime of the caller's locals
before the call; code that uses `musttail` must drop it to be verified.

2026.11.21: `translation_unit` has a new field `dropped_symbols : list name`,
the names of the symbols that `cpp.prog` dropped (see below). `sub_module`
ignores it. Code that calls `makeTranslationUnit` positionally needs an extra
argument, usually `[]`. `supported.report.all` lists each dropped symbol as
"unsupported", with the gap "name may denote several entities", and
`supported.report.run` gives that verdict, rather than "missing", to a root
that resolves to a dropped symbol: by its printed name (as `all` prints it),
or by parsing to a name that agrees with it outside its unsupported parts
(e.g. `f(long double*)` for `f(?Builtin long double*)`).

2026.11.20: parser.v drops every symbol, and makes every type
`Gunsupported`, whose name contains an unsupported atom (`has_unsupportedN`),
such as `?record` for an unnamed struct or lambda closure at global scope, or
`Aunsupported` for a floating-point template argument. Such a name may denote
several entities, and their equal definitions used to merge into one global.
Proofs about these entities, which were unsound, no longer go through. This includes names
that mention an unsupported type such as `Tunsupported "Builtin long double"`,
e.g. functions taking `long double` and libstdc++'s `long double`
instantiations: `cpp.spec` finds no symbol for them.

2026.11.19: Records with bit-fields become *opaque records*
([#307](https://github.com/SkyLabsAI/BRiCk/issues/307)).
- `GlobDecl` has a new constructor `Gopaque (_ : Opaque)`, and the parser a new
  declaration `Dopaque`. An `Opaque` carries the record's size, alignment,
  destructor, trivial destructibility, `operator delete`, and the reason its
  body is not modeled, but no members or bases. Exhaustive matches on
  `GlobDecl` need a new case.
- cpp2v emits `Dopaque` instead of `Dunsupported` for a complete C++ record
  with a bit-field and no virtual base. Such a type has a `size_of` and an
  `align_of`, is a `complete_type`, and is destroyed by calling its destructor;
  previously it had no size, was not a complete type, and could
  not be passed by value or destroyed.
- `supported.check` accepts a translation unit with an opaque record.
  `supported.report` lists it as a `partial` gap, and member access into it as
  `unsupported`.

2026.11.19: `wp_method` of a union's defaulted copy/move assignment operator
is now a disjunction: the existing copy (`anyR` of the destination plus
`wp_union_copy`) or, when the source reference is `this` itself,
self-assignment (`wp_union_self_copy` in `logic/func.v`), which takes full
ownership of the union's active member as raw bytes (`unionR`, `rawsR`) and
gives it back unchanged. Proofs of such copies now pick a disjunct first.

2026.11.05: Add Clang 23 support for the `cpp2v` binary.

2026.10.29: C++ name/type notation now parses and prints array declarators
with C++ precedence and dimension order ([#448](https://github.com/SkyLabsAI/BRiCk/issues/448),
[#453](https://github.com/SkyLabsAI/BRiCk/pull/453)).
- Array references use `int(&)[3]`; the malformed `int[3]&` spelling is rejected.
  Update affected `%cpp_name` and `%cpp_type` literals to the valid spelling.
- Multidimensional arrays use outermost-first dimensions: `int[5][10]` means
  five arrays of ten integers. Literals that relied on the previous reversed
  order must reverse their dimensions to preserve their intended type; for
  example, two zero-length byte arrays are now `unsigned char[2][0]`.
- Omitted array bounds are allowed only for the outermost dimension of each
  array type: `int[][3][4]` is valid, while `int[][][4]` is rejected. Pointers
  to unknown-bound arrays, including arrays of such pointers, remain supported.

2026.10.27: cpp2v prints a union's defaulted copy/move constructors and
copy/move assignment operators as `Defaulted` instead of clang's AST body
(empty, resp. `return *this;`: clang's code generator performs the copy at the
call site, so executing that body copied nothing). `wp_ctor` and `wp_method`
give these members the meaning of copying the object representation
(`wp_union_copy` in `logic/func.v`): the source's active member and its raw
bytes (`unionR`, `rawsR`) become the destination's; the byte list has exactly
the member's `size_of`. Proofs about such copies must now supply the source as
raw bytes (`primR_to_rawsR`) and the destination as `anyR` (assignment) or
`tblockR` (construction). Unions with a `[[no_unique_address]]` member are
excluded: their copy/move operations get no body, because the member's
`size_of` can exceed the bytes clang copies.

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


