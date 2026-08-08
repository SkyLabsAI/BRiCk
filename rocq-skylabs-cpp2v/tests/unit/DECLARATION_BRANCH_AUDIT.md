# Phase 4C declaration/root branch audit

This is the implementation checklist for replacing `PrintDecl.cpp` with owned,
final-core IR. `syntax/mtraverse.v` is the recursive-field order authority;
parser/mparser declaration helpers are evaluated while building and never
appear as owned constructors.

## Final records and recursive child order

| Final value | Recursive children, in order | Scalar/container-only fields |
|---|---|---|
| `global_init.Init e` | `e` | other global-init alternatives are nullary |
| `Impl s` | `s` | `Builtin name` has only its string |
| `Build_Func` | return type, parameter types, present function body | parameter local names, calling convention, arity, exception spec |
| `Build_Method` | return type, class name, parameter types, present `OrDefault` body | this qualifiers, parameter identifiers, calling convention, arity, exception spec |
| `InitBase` / `InitField` / `InitIndirect` | class name / atomic field name / each path field+class then final field | `InitThis` is nullary; list/product wrappers add no nodes |
| `Build_Initializer` | path, expression | none |
| `Build_Ctor` | class name, parameter types, present body wrapper; a present user/compiler body contains initializers then statement | parameter identifiers, calling convention, arity, exception spec |
| `Build_Dtor` | class name, present body wrapper, then body statement if present | calling convention, exception spec |
| `Build_LayoutInfo` | none | layout offset |
| `mkMember` | field atomic name, type, optional in-class initializer, layout record | mutable flag |
| `Build_Union` | members, destructor name, optional delete name | trivial flag, size, alignment |
| `Build_Struct` | base names, members, virtual method names/implementations, override names, destructor name, optional delete name | base offsets, trivial flag, layout kind, size, alignment |
| `Ovar` | type, global-init value | none |
| `Ofunction` / `Omethod` / `Oconstructor` / `Odestructor` | corresponding record | none |
| `Gunion` / `Gstruct` | corresponding record | none |
| `Genum` | underlying type | enumerator identifiers |
| `Gconstant` | type, optional expression | none |
| `Gtypedef` | type | `Gtype` nullary; `Gunsupported` has only its message |
| `Template` roots/aliases | each parameter and present default in source/context order, then final value/type | list/product/option wrappers add no nodes |
| `TPreInst` | target name, template arguments | list wrapper adds no node |

`OrDefault`, function-body, global-initializer, and `Build_LayoutInfo`
alternatives are real owned nodes, not opaque text. The optional/list/product
containers around them are not nodes. Layout records are compiler-provided
nodes with synthesized origins anchored to the owning field/base rather than
fake written occurrences.

## Clang declaration dispatch

- `VarDecl`: final `Ovar`; type precedes the chosen `global_init` alternative.
  External, delayed static-local, explicit initializer, implicit template
  initializer, and no-init cases match `PrintDecl.cpp` exactly.
- Free function/method/constructor/destructor: final record and `ObjValue`.
  A static method is eagerly converted to final `Ofunction (static_method m)`;
  the erased class/this/body-wrapper fields do not remain location children.
  Unevaluated exception specifications are resolved through the live `Sema`
  before body inspection, matching the legacy printer's ordering and values;
  selecting such a declaration without `Sema` is a recoverable error.
- Parameters are source ordered. Written parameter types are used where
  available without changing the legacy semantic value.
- Constructor initializers retain Clang initialization order. Template
  `Einitializing_type` is reduced eagerly; member/base/indirect/delegating paths
  are structured final values.
- C++ struct/union definitions own fields/layout/bases/virtuals/overrides;
  forward declarations become `Gtype`. Override pairs are emitted only for
  virtual non-pure overriding methods, exactly like `PrintDecl.cpp`. Bitfields,
  invalid fields, and virtual bases retain the exact unsupported-declaration
  boundary. Complete non-C++ `RecordDecl` definitions are an explicit
  recoverable boundary: the legacy C branch supplies `None` where final
  `Build_Struct`/`Build_Union` requires a destructor name, so no fake name is
  invented. The Phase 4C input and parity scope is C++17/C++20.
- Enums own the written underlying type and scalar enumerator names. Ordinary
  enum constants are eagerly reduced to final `Gconstant (Tenum ...) (Some
  (Ecast ... literal))`; the legacy helper's redundant initializer argument is
  erased. Constants in template scopes remain the legacy zero-node boundary,
  even when their underlying type is concrete, while their enclosing enum root
  is retained.
- Typedefs become final `Gtypedef`; template aliases become typed non-root
  template-alias events. Anonymous-name and self-typedef suppression remains at
  the ModuleBuilder/event-selection seam.
- Template declarations own final `(parameter, default)` entries. Template
  specializations produce a canonical ordinary instance key and final
  `TPreInst` non-root event rather than retaining `Dinstantiation`/`untempN`.
- Nondependent static assertions own their final expression and optional
  message in a non-root event. Namespace aliases/global namespace inclusions
  own names and declaration origins. Production aliases use the same reverse
  qualified-name ordering helper as the legacy backend, never pointer order.

## Root and event order

The caller supplies declarations in the same partition/order already selected
by `ModuleBuilder`: ordinary declarations, ordinary definitions, template
declarations, template definitions. A declaration can return zero, one, or
several roots (implicit special members precede the C++ record root). Static
specializations are ordinary roots and their Template-mode occurrences become
instance events. Root values are final `ObjValue`, `GlobDecl`, or `Template`
values; parser wrappers such as `Dfunction`, `Dstruct`, and implicit-member
helpers do not exist in the arena. Rocq folds remain the sole duplicate winner
selection mechanism.

Sharing seeds follow declaration order. Ordinary declaration values are visited
before their names, with `VarDecl` omitting the root-name seed as legacy
`PrePrint` does; Template-only seeds never create new definitions.

## Provenance policy

- Written declaration root/name/record occurrences retain direct explicit
  declaration origins; implicit Clang declarations use implicit origins.
- Nested written fields, bodies, initializers, parameter and return types,
  enum underlying types, and base types retain their own occurrences. A base
  layout record is synthesized directly from the corresponding written base
  origin, not from the owning record declaration.
- Parser-generated wrappers, eager helper expansions, default-body wrappers,
  enum constant cast/literal nodes, generated record destructor names, and
  implicit-member final roots are synthesized/implicit as appropriate and
  directly anchored to the controlling written declaration.
- Erased helper levels contribute transformed provenance but no semantic child;
  in particular, the final static-method `Ofunction`/`Build_Func` occurrences
  retain a transformed origin derived from the written method.
- Every selected declaration/non-root event is fully owned before Clang dies;
  emitters and duplicate folds receive no Clang pointer or formatter callback.

## Required focused evidence

1. Pure checked factories: exact rendering, all malformed categories, and exact
   flattened children for every record/root/event constructor above.
2. Independent C++17/C++20 legacy equality for declarations and definitions of
   every family, including static methods, pure overrides,
   incomplete/complete records, explicit/default/compiler-provided bodies,
   actual and parser-fallback implicit destructors, resolved exception specs,
   global init alternatives, enums, typedefs, templates, and specializations.
3. Structural provenance checks for exact written return/base/enum offsets,
   base-layout anchors, fields/layout-generated pieces, generated destructor
   names, constructor initialization order, implicit members, static-method
   transformed derivations, enum helper reduction, and template
   parameter/default order.
4. Ordered root/non-root event and production-sharing seed checks against the
   ModuleBuilder partitions, including reverse-qualified alias order, static
   assertions, self-typedef suppression, template-scope enum-constant
   suppression, static/template specialization duplication, and template
   overwrite order.
5. Full legacy backend and frozen semantic-output regressions before Phase 5.
