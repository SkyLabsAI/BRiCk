# Pure cpp2v IR unit tests

`IRTests.cpp` is a deliberately tiny, no-third-party runner. It prints only
failing table entries and is executed from the workspace root with:

```text
dune build @cpp2v-unit-tests
```

## AST-evolution maintenance rule

The constructor registry is part of the public location-path ABI. Whenever a
BRiCk semantic constructor gains, loses, or reorders a recursive field, update
all of the following in the same change:

1. `ir::Constructor` and its sole `ConstructorSpec` entry;
2. the complete lossless `ValueShape`, including scalar companions and
   option/list/product/sum grouping;
3. the exact `Arena::children` flatten-order cases in `IRTests.cpp`; and
4. the frozen location-path documentation and affected lookup fixtures.

Registry entries marked `testOnly` are Auxiliary grouping fixtures, cannot be
roots or event payloads, and have matching smoke definitions in `fixtures.v`.
Every non-test entry names a real BRiCk constructor.

Phase 2 emitters intentionally produce validated projection/event fragments for
manually built IR. They are not standalone generated `.v` files: imports, ABI,
`source`/`module` composition, and stable `source_locations` belong to Phases 5
and 6.

Phase 3 Clang `SourceManager`/`Lexer` extraction is implemented separately in
`cpp2v-clang-source` and exercised by `SourceInfoProbe.cpp` through
`@cpp2v-source-info-tests`. The pure `IRTests.cpp` target remains Clang-free.

Phase 4A sharing metadata stores only strong owned class IDs. Pure
`IRSharing::analyze` consumes ordered ordinary/template-only seeds after the IR
is finished and never mutates nodes or location shape. Clang canonical-identity
capture and stable static/meta rendering are exercised separately by
`SharingBuilderProbe.cpp` and `@cpp2v-sharing-builder-tests`.

Phase 4B pure coverage constructs final cast, operator, call/member,
construction, initialization, cleanup/materialization, array-loop,
allocation/deallocation, lambda/capture, atomic, `va_arg`, conditional,
GNU-conditional, `offsetof`, local declaration/binding, and statement trees
only through checked factories. It validates every product/sum/list/option
shape and exact `Arena::children` order. `TypeExprBuilderProbe.cpp` separately
proves Clang lowering against the independent legacy printer in C++17 and
C++20, checks zero/one/forwarded/several statement cardinalities and synthetic
origin anchors, and exercises `if consteval` structurally in C++23. Static VLA
capture remains exactly equal to the legacy oracle; Template VLA capture
finalizes the legacy printer's ill-typed missing `Eunsupported` type argument
as `Tauto` and compiles as final core IR.

Phase 4C adds checked final-core declaration records, explicit layout nodes,
typed non-root events, and one ordered root/non-root event stream.
`DeclarationBuilderProbe.cpp` exercises both direct focused selections and the
`ModuleBuilder` partition adapter, including parser-generated implicit-member
fallbacks, actual compiler-provided members (including the destructor),
static-method and enum-helper reduction, pure-virtual override filtering,
template-scope enum-constant suppression, live-Sema exception resolution,
reverse-qualified namespace-alias order, duplicate ordinary roots, template
overwrite, static assertions, template aliases/instances, exact written and
generated declaration provenance, the explicit complete-C-record rejection
boundary, and production sharing seeds. The declaration Cram compiles all
emitted terms and proves C++17/C++20 equality against independently generated
legacy static and template maps.

Phase 5 made the owned builder/emitter path the sole production semantic
implementation. `ToCoq` constructs one finished `TranslationUnitIR`; ordinary,
template, simultaneous, and interactive semantic modes share it and one
ordinary-seeded sharing plan. The legacy formatter is retained only as the
transitive diagnostic closure used by `--name-test`; declaration emission and
semantic preprint callbacks are intentionally absent and mechanically checked
by `@cpp2v-architecture-tests`.

Phase 6 location output consumes that same finished unit. The companion emitter
walks the authoritative ordered root-event stream, renders semantic names and
values inline, and obtains every recursive location child exclusively from
`Arena::children`. It has no Clang, sharing-plan, or constructor-specific shape
access. The generated Rocq fold reuses semantic table selection and rejects an
incompatible concrete event stream at compilation time.

Phase 7 production Crams cover path/arity, macro and file fidelity, `#line`,
implicit/synthetic/transformed origins, templates and POIs, redeclarations,
all four root namespaces, unsupported/invalid provenance, determinism, sharing,
and a non-golden scaling smoke. Compatibility boundaries remain final core:
erased wrappers append transformed origins to surviving nodes; generated nodes
use explicit anchors/derivations; deferred dependent semantics use narrow typed
unsupported values; and unrelated malformed or nondependent cases remain hard
builder errors.

The current API intentionally has no zipper, ancestor fallback, isolated-value
lookup, stale-pair check, or locations for non-name-keyed translation-unit
metadata. Tests must not fabricate any of those behaviors or add semantic
sharing identities to location paths as a workaround.
