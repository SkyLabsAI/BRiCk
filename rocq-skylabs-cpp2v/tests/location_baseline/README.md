# Source-location migration baseline

This directory freezes the semantic-output baseline and path contract before the
source-location IR migration.  It is deliberately not a Cram test: `default.v`
and `no-sharing.v` are checked oracle inputs for old/new semantic equality.

## Frozen path contract

A location root is exactly the semantic value stored in one of the four tables:
ordinary symbol, ordinary type, template symbol, or template type.  The overlay
does not add a declaration node above that value.

A location node exists for each source-relevant semantic constructor or record
occurrence.  Lists, options, products, sums, scalar fields, formatter syntax,
and local sharing definitions do not create nodes.  Children are recursive
fields in semantic declaration order.  Required children contribute one node;
`Some` contributes one and `None` zero; lists preserve element order; products
and active sums flatten relevant payloads left-to-right.  Paths are zero-based,
root-to-leaf lists: `[]` selects the root and `i :: rest` selects child `i`.

Canonical examples:

- `Ebinop op lhs rhs ty` has children `[lhs; rhs; ty]`.
- `Ecall fn args` has `fn` followed by each argument.
- `Sif init decl test then_branch else_branch` has each present optional child,
  then `test`, `then_branch`, and `else_branch`.
- `Func` has return type, parameter types, and a present body wrapper.
- `Ofunction f` has the `Func` record as its only child.
- `Template params value` has each parameter and present default in declaration
  order, followed by `value`.

Sharing is transparent: unfolding `n1`/`t1` defines the path shape, so
`--no-sharing` may change semantic text but never a location tree.

## Representative corpus

`fixture.cpp` intentionally covers all Phase 0 categories:

| Requirement | Fixture construct |
|---|---|
| nested statements/expressions | `Record::method` and `redeclared` |
| record fields/implicit members | `Record` and `Box<T>` |
| enum/constants | `Kind`, `KZero`, and `KOne` |
| ordinary/template functions/types | `redeclared`, `twice<T>`, and `Box<T>` |
| redeclaration/definition | the two declarations of `redeclared` |
| type/name sharing | repeated `int`, `Record`, and function/type names |

The baseline was generated from the workspace root with:

```sh
_build/install/default/bin/cpp2v --locations-inline=false \
  -o fmdeps/BRiCk/rocq-skylabs-cpp2v/tests/location_baseline/default.v \
  fmdeps/BRiCk/rocq-skylabs-cpp2v/tests/location_baseline/fixture.cpp -- \
  -std=c++17
_build/install/default/bin/cpp2v --no-sharing --locations-inline=false \
  -o fmdeps/BRiCk/rocq-skylabs-cpp2v/tests/location_baseline/no-sharing.v \
  fmdeps/BRiCk/rocq-skylabs-cpp2v/tests/location_baseline/fixture.cpp -- \
  -std=c++17
```

These semantic-only migration baselines deliberately opt out of the current
default inline location section so their historical hashes continue to isolate
AST serialization.

Frozen SHA-256 values:

```text
8353389dbc1a7f808343017baceff6cf40bb189e56f0effb1b9ccc145e74347b  default.v
c443a6d57a84205f8127b55caa6d871633be8b7c508166767f642c40b1e98d4b  no-sharing.v
```

## Parser-only helper inventory

The following helper names are emitted by the legacy printer and therefore must
be evaluated while building final IR values.  “Erased” means the helper reduces
to an argument; “normalized” means it changes or infers a semantic value;
“expanded” means it constructs a different subtree; “insertion” means it
constructs or inserts a final top-level value.

| Legacy source | Classification | Helpers |
|---|---|---|
| `PrintName.cpp` | normalized | `Nfunction`, `Nctor`, `Nop`, `Nop_lit`, `Ndependent`, `Nlocal` |
| `PrintName.cpp` | renamed core leaf | `Nrecord_by_field`, `Nenum_by_enumerator`, `Nby_first_decl` |
| `PrintType.cpp` | erased | `Talias`, `Tunderlying`, `Tunary_xform`, `Tdecay_type` |
| `PrintType.cpp` | normalized | parser notation `Tfunction`; `Qconst`, `Qvolatile`, `Qconst_volatile` |
| `PrintExpr.cpp` | erased | `Eextension`, `Esource_loc`, `Edefault_init_expr` |
| `PrintExpr.cpp` | expanded | `Ecstyle_cast`, `Efunctional_cast`, `Edynamic_cast`, `Estatic_cast`, `Econst_cast`, `Ereinterpret_cast`, `Ebuiltin_bit_cast`, `Egnu_null`, `Enoexcept`, `Efloat_of_bits`, `Ealignof_preferred`, `Esizeof_pack`, `Eoperator_member_call`, `Eoperator_call`, `Eenum_const_at`, `Ebuiltin`, `Emember`, `Eunevaluated_var`, `Ecapture_var`, `Ecapture_this`, `Econcept_specialization`, `Estring` |
| `PrintExpr.cpp` (template mode) | inferred/expanded | `Eassign`, `Eassign_op`, `Esubscript`, `Ebinop`, `Ecomma`, `Eseqand`, `Eseqor`, `Eunop`, `Epreinc`, `Epredec`, `Epostinc`, `Epostdec`, `Ederef`, `Eunresolved_member`, `Eunresolved_call`, `Eunresolved_delete`, `Einitializing_type` |
| `PrintStmt.cpp` | renamed core | `Sreturn_void`, `Sreturn_val` |
| `PrintStmt.cpp` | expanded | `Sforeach` |
| `PrintLocalDecl.cpp` (template mode) | transformed | `Dvar` |
| `PrintDecl.cpp` | insertion/final-value wrappers | `Dvariable`, `Dfunction`, `Dmethod`, `Dconstructor`, `Ddestructor`, `Dtype`, `Dunsupported`, `Dstruct`, `Dunion`, `Denum`, `Denum_constant`, `Dtypedef`, `Dstatic_assert` |
| `PrintDecl.cpp` | synthesized insertion | `Oimplicit_default_ctor`, `Oimplicit_copy_ctor`, `Oimplicit_move_ctor`, `Oimplicit_copy_assign`, `Oimplicit_move_assign`, `Oimplicit_dtor` |
| `PrintDecl.cpp` (template mode) | insertion/final-value wrappers | `Dtemplated_variable`, `Dtemplated_function`, `Dtemplated_method`, `Dtemplated_constructor`, `Dtemplated_destructor`, `Dtemplated_type`, `Dtemplated_unsupported`, `Dtemplated_struct`, `Dtemplated_union`, `Dtemplated_enum`, `Dtemplated_enum_constant`, `Dtemplated_typedef`, `Dtemplated_static_assert`, `Dinstantiation` |
| `ToCoq.cpp` | non-root insertion | `Dinline_namespace`, `Dusing_namespace`, `Dglobal_using_namespace`, `Dstatic_assert` |

Core constructors that happen to be re-exported from parser modules are not
listed as parser-only helpers.

## Raw semantic writes bypassing `CoqPrinter::ctor`

These legacy writes must move behind typed scalar/constructor factories.  The
inventory includes nullary semantic constructors and enum-like scalar payloads:

```text
PrintDecl.cpp:527  POD
PrintDecl.cpp:529  Standard
PrintDecl.cpp:531  Unspecified
PrintDecl.cpp:639  POD
PrintDecl.cpp:822  InitThis
PrintExpr.cpp:99   OO<Name> (macro-generated overloadable operators)
PrintExpr.cpp:203  Tauto
PrintExpr.cpp:222  Tauto
PrintExpr.cpp:975  Tchar
PrintExpr.cpp:1097 Rarrow
PrintExpr.cpp:1169 Virtual
PrintExpr.cpp:1171 Direct
PrintExpr.cpp:1355 Enull
PrintLocalDecl.cpp:50 Derror
PrintName.cpp:643  Enull
PrintName.cpp:820  Ndtor
PrintName.cpp:1009 Nanonymous
PrintName.cpp:1172 Ndtor
PrintName.cpp:1364 Ndtor
PrintStmt.cpp:137  Sbreak
PrintStmt.cpp:142  Scontinue
PrintStmt.cpp:167  Sskip
PrintStmt.cpp:212  Sdefault
PrintStmt.cpp:282  Sreturn_void
PrintStmt.cpp:300  Sskip
PrintType.cpp:176  Tauto
PrintType.cpp:187  Tauto
PrintType.cpp:266  Tauto
PrintType.cpp:336  Mtype/type (sort argument)
PrintType.cpp:647  QCV
PrintType.cpp:649  QC
PrintType.cpp:653  QV
PrintType.cpp:655  QM
```

## Baseline environment and checks

Recorded revisions and tools:

```text
workspace  9d4bec2ca26a5e5566cc87388701cfb3246c7070
BRiCk      26681a34598aaf632b3415ca6668307025bd517c
LLVM       22.1.3 (cpp2v link/runtime)
Clang      18.1.8 (fixture driver/resource headers)
Rocq       9.2
Dune       3.22.2
CMake      4.3.1
C++        GCC 15.2.1 20260209
Target     x86_64-unknown-linux-gnu
BUILD_TYPE unset (Dune default: Debug)
BUILD_ARGS unset
```

Sequential green checks before production edits:

```text
UV_CACHE_DIR=/tmp/uv-cache-janno dune build @cpp2v                         PASS
UV_CACHE_DIR=/tmp/uv-cache-janno dune runtest .../tests/deterministic.t   PASS
rocq c <temporary-copy-of-default.v>                                      PASS
UV_CACHE_DIR=/tmp/uv-cache-janno dune build .../templated_declarations.vo PASS
```

The first composed build attempt exposed a read-only default `uv` cache; using a
writable `/tmp` cache fixed that environment issue.  A full cpp2v Cram baseline
also exposed a pre-existing nested-Dune sandbox issue: the inner test workspace
sees `skylabs/cpp/stdlib/algorithms/spec.vo` as a broken relative install link
while an equivalent direct temporary project compiles successfully.  This is
recorded as baseline infrastructure evidence rather than promoted output.
