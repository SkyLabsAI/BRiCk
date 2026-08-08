# Phase 4A name/type builder branch audit

This table is checked against `src/PrintName.cpp` and `src/PrintType.cpp`.
“Final” means the builder creates the core BRiCk value; “erased” means the
legacy parser helper/sugar is evaluated by cloning the selected child and
adding transformed provenance; “unsupported” means the final core
`Tunsupported`/`Nunsupported` value is built. Only expression families assigned
to Phase 4B may still return `migration incomplete`.

## Names (`PrintName.cpp`)

| Legacy family | IR disposition |
|---|---|
| identifiers; namespaces; records; enums; aliases; typedefs; variables; fields; bindings; enum constants | Final `Nid`/`Nglobal`/`Nscoped`; function-body duplicates use the legacy `name`, `name'0`, … traversal |
| anonymous namespace | Final `Nanonymous` |
| anonymous tag by typedef, following declaration, first field/enumerator, or context index | Final `Nid`, `Nfirst_decl`, `Nfirst_child`, or `Nanon`; unreferenceable global anonymous tags are explicit migration errors at the experimental selection boundary |
| functions, methods, constructors, destructors, conversions, overloaded/literal operators | Final core `Nfunction`, `Nctor`, `Ndtor`, `Nop`, `Nop_conv`, `Nop_lit`; argument normalization is performed in C++ (`BuildName.cpp`, `functionAtomicName`). Structured `OONew`/`OODelete` array flags are owned values, not scalar text. |
| primary class/function/variable/alias templates | Final `Ninst` with synthesized parameter-as-argument occurrences |
| class/partial/variable specializations | Final single `Ninst` around an undecorated base name and actual ordered arguments; `getTemplateArgsAsWritten` supplies exact argument locations when present (`BuildName.cpp`, `buildSpecialization`). |
| function specializations | Final single `Ninst`; primary scope identity is combined with the specialization declaration's substituted atomic parameter types and `getTemplateSpecializationArgsAsWritten` locations (`BuildName.cpp`, `buildSpecialization`). |
| `Nlocal` | Evaluated to final `Nglobal` for unqualified unresolved names |
| smart `Ndependent` | Evaluated to the underlying name for `Tnamed`; otherwise final core `Ndependent` |
| namespace/type nested-name specifiers | Final recursively scoped/dependent name |
| every other atomic declaration kind; Microsoft `__super`; non-identifier unresolved declaration names | Exact legacy `Nunsupported_atomic`/`Nunsupported`, or a recoverable expression-kernel error only when the enclosing expression belongs to Phase 4B |

## Types (`PrintType.cpp`)

| Clang / legacy family | IR disposition |
|---|---|
| bool, void, nullptr, integers, chars, float/double/float16/float128 | Final core leaf |
| long double | Final `Tunsupported` (legacy BRiCk layout policy) |
| dependent builtin / unresolved auto | Mode-specific final `Tauto` in template mode, final `Tunsupported` in static mode |
| other sizeless builtins | Final `Tarch None name` |
| other builtins | Final `Tunsupported` |
| const/volatile | Final `Tqualified`; non-cv qualifiers ignored/erased as in legacy |
| pointer, lvalue/rvalue reference, constant/incomplete/variable/dependent array, member pointer | Final recursive core constructor with nested `TypeLoc` provenance; an unresolved member-pointer qualifier is an exact diagnostic `Tunsupported` class child while the outer member-pointer and pointee remain final |
| function prototype | Final core `Tfunction (@FunctionType _ cc arity return params)`; parameters are normalized/adjusted in C++ |
| enum / record / template parameter | Final `Tenum`, `Tnamed`, `Tparam` |
| dependent name | Final `Tnamed` over a final unresolved name |
| template specialization | Alias/sugar erased; unsugared ordinary and template-template applications expand to `Tnamed (Ninst ...)` (the `Tparam_inst` abbreviation is never stored) |
| injected class name | Final `Tnamed` of the template-aware declaration name |
| attributed, parenthesized, typedef, substituted parameter, macro-qualified, using, predefined sugar | Erased with a distinct cloned occurrence and transformed provenance |
| decay | Parser `Tdecay_type` evaluated to the adjusted final type with transformed provenance |
| unary transform | Nondependent helper evaluated to the final underlying type; dependent legacy-unsupported form becomes final `Tunsupported` |
| deduced type | Every non-null deduced result is erased regardless of dependence; a null deduced result is final `Tauto` (distinct from the mode-sensitive `AutoType` row) |
| decltype | Sugar erased; unsugared template mode is final `Texprtype`/`Tdecltype`; static mode is final `Tunsupported` |
| typeof expression | Sugar erased; unsugared template mode is the expression type; static mode is final `Tunsupported` |
| elaborated type (Clang < 22) | Named type erased; null named type is exact `Tunsupported "elaborated type w/ null"`; this conditional legacy branch is audited but is unavailable to the Clang 22 fixture |
| block pointer, pack expansion, vector, and any unrecognized Type node | Final `Tunsupported` with the exact legacy `TypeClassName + diagnostic QualType` payload (`BuildType.cpp`, `describeType`) |

## Deliberately deferred to Phase 4B

Calls, member access, general casts, construction and initialization, new/delete,
lambdas, assignment/logical/comma sequencing, character/floating literals,
and statements remain recoverable `migration incomplete` expression branches.
The Phase 4A kernel owns literals already required by types/defaults, named and anonymous local/global/static-local/template/dependent references, enum constants, written unary address-of expressions, `Cl2r` implicit conversions required by operands, and arithmetic/comparison unary/binary forms. Dependent/unresolved names and direct non-type-template-parameter references are final only in template mode; direct static selections are recoverable boundaries unless Clang has supplied a substitution wrapper. Canonical `TemplateArgument::Declaration` deliberately remains `Avalue (Eglobal/Evar …)` because legacy `PrintName.cpp:645-658` calls `printValueDeclExpr` directly; only an as-written `&decl` expression contains `Eaddrof`.

Variable/dependent arrays and `decltype`/`typeof` call this kernel recursively. A bound or operand from the completed kernel yields a final type. A call/member/construction/general-cast operand returns the documented Phase-4B expression error; the type visitor itself has no separate missing branch. This is the precise Phase-4A.2/4B recursion boundary, not a claim that Phase-4A.2 implements arbitrary expressions.

## Checked evidence

- `tests/type_expr_builder_cram/type_expr_builder.t/run.t` Rocq-compiles every selected final name/type/expression/parameter/argument/default value. Before the Phase 5 switch, the independent legacy parity probe proved exact equality for all selected static/template types, expression-kernel values, parameters, defaults, arguments, and the partial-specialization declaration; that obsolete semantic implementation was then removed. The distinct `--name-test` diagnostic path still provides exact-membership coverage for primary class/function/variable/alias templates, concrete specializations, normalized functions, constructors/destructors/conversions/operators, and allocation operators.
- `tests/unit/TypeExprBuilderProbe.cpp` checks exact specialization argument offsets, recursive dependent qualifier `TypeLoc`s, inherited-default anchors/derivations, every recursive function/member type child, declaration and pack argument order, implicit `Cl2r` origins, static/template expression boundaries, deduction-guide dispatch, structural-argument fallback, and the constructor disposition of unary-transform, deduced/auto, decltype, decay, injected, template-template, vector, block-pointer, and pack-expansion cases.
- `tests/unit/IRTests.cpp` checks final named/anonymous local, address-of, `Cl2r`, builtin-cast, and function-record rendering plus selected-node validation failures. The builder probe additionally covers exact `Aunsupported` kind names, canonical bare declaration arguments versus written address-of, synthesized omitted specialization arguments, reference/binding declaration types, resolved value-dependent arithmetic, enum constants/integral casts, and a completed variable-array bound.
- The architecture/sizeless builtin row is implemented through `Tarch`; the C++17 host fixture cannot spell a portable target-independent sizeless builtin, so that environment-dependent branch is covered by the branch audit rather than a host-specific fixture.
- `grep` over `BuildType.cpp` leaves recoverable errors only for invalid null API input or documented recursive calls into Phase-4B expression families; every non-null Clang `Type` otherwise reaches a final core value, an erased clone, `Tarch`, or exact `Tunsupported`.
