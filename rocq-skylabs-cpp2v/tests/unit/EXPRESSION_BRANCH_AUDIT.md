# Phase 4B expression builder branch audit

This checked audit compares `src/BuildExpr.cpp` with legacy
`src/PrintExpr.cpp` and BRiCk's `parser/expr.v`. “Final” means the owned IR is
the post-parser core value. “Erased” means the final child occurrence is cloned
with transformed wrapper provenance and no semantic level is added.

## 4B.1 family 1 — casts and literal-like expressions

| Legacy/Clang family | Owned final IR disposition |
|---|---|
| implicit casts | `Ecast descriptor operand`; the root and descriptor are implicit occurrences |
| C-style cast | `Eexplicit_cast cast_style.c written_type (Ecast descriptor operand)` |
| functional and builtin bit-cast | `Eexplicit_cast cast_style.functional written_type (Ecast descriptor operand)` |
| `static_cast`, `dynamic_cast`, `reinterpret_cast`, `const_cast` | `Eexplicit_cast` with the corresponding final `cast_style` and nested `Ecast` |
| bit/lvalue-bit/lvalue-to-rvalue-bit/no-op | `Cbitcast`, `Clvaluebitcast`, `Cl2r_bitcast`, `Cnoop` with final declaration type |
| lvalue-to-rvalue, array/function decay | final nullary `Cl2r`, `Carray2ptr`, `Cfun2ptr` |
| integral/pointer/boolean conversions | final `Cint2ptr`, `Cptr2int`, `Cptr2bool`, `Cintegral`, `Cint2bool` |
| floating conversions | final `Cfloat2bool`, `Cfloat2int`, `Cint2float`, `Cfloat` |
| null pointer/member-pointer | final `Cnull2ptr`/`Cnull2memberptr` with result type |
| builtin function conversion | only enclosing `CK_BuiltinFnToFnPtr` eagerly becomes final `Ecast (Cbuiltin2fun (Tptr function_type)) (Eglobal name function_type)`; a bare/unevaluated builtin `DeclRefExpr` remains ordinary `Eglobal` as in legacy |
| constructor/user/to-void/dynamic/dependent | final `Cctor`, `Cuser`, `C2void`, `Cdynamic`, `Cdependent` descriptors; later-family operands remain recoverable boundaries |
| derived/base paths | final `Cderived2base`/`Cbase2derived`; ordered intermediate types precede the final declaration type |
| every other `CastKind` | exact final `Cunsupported castKindName declaration_type`, never opaque |
| any non-C++ explicit-cast subclass not recognized by the legacy explicit dispatcher | exact final legacy `Eunsupported StmtClassName declaration_type` without recursing into a later-family operand |
| integer/bool/nullptr | final `Eint`/`Ebool`/`Enull` |
| ordinary/wide/UTF character literals | final `Echar` with the Clang code unit and exact character type |
| float16/float/double/float128 literals with matching semantics | final `Efloat ft (float_value.of_bits ft bits)` |
| unsupported float semantics, including long double | exact legacy `Eunsupported` diagnostic and final declaration type |
| ordinary/wide/UTF string literals | final core `Estring (literal_string.of_list_N code_units) element_type`; native-endian code units and no trailing NUL match legacy |
| GNU `__null` | eager final `Ecast (Cptr2int result_type) Enull` |
| `SourceLocExpr` | parser helper erased: evaluated integer/string final value with synthetic plus transformed provenance |
| `PredefinedExpr` | final core string value; missing function name is final `Eunresolved_string_literal Tchar` |
| `noexcept` and nondependent type traits | parser helpers evaluated to final `Ebool` |
| dependent type traits, imaginary/fixed-point literals | exact final legacy `Eunsupported diagnostic declaration_type`; `Location.cpp`'s `loc::describe` `Stmt` case is exactly `getStmtClassName()`, which is the builder payload |
| `ConstantExpr`, parentheses, unary extension, `CXXDefaultInitExpr` | erased clone with transformed provenance |
| `CXXBindTemporaryExpr`, substituted non-type parameter | legacy-erased clone with transformed provenance |

Explicit-cast helper expansion accepts exactly BRiCk's six `cast_style`
constructors (`functional`, `c`, `static`, `dynamic`, `reinterpret`, `const`)
and has child order `written type`, then inner `Ecast`; the inner cast has
`Cast`, then operand. Cast descriptors expose every
recursive type/path child through `Arena::children`.

## 4B.1 family 2 — built-in operator syntax

| Legacy/Clang family | Owned final IR disposition |
|---|---|
| `UnaryOperator` `+`, `-`, `~`, `!` | final `core.Eunop` when mparser supplies a result type, otherwise final `Eunresolved_unop` in template mode; dependent `T *` unary plus reproduces mparser's exact `Tlonglong` special case |
| unary `__real`, `__imag`, and any Clang `co_await` unary node | exact final `core.Eunop (Uunsupported opcode)` or template `Eunresolved_unop (Runop (Uunsupported opcode))`, never a fake supported operation |
| unary `*`, pre/post `++`/`--` | final `core.Ederef`, `core.Epreinc`, `core.Epostinc`, `core.Epredec`, `core.Epostdec`, each with operand then result type; mparser's dependent-pointer increment/decrement cases remain resolved while dependent dereference remains unresolved |
| unary `&` | final `Eaddrof`; non-static field/method addresses are explicitly rejected at the calls/members boundary because legacy requires `Eglobal_member` |
| unary extension and rewritten binary syntax | erased clone of the semantic child with transformed provenance when that child is in the migrated family; a rewritten semantic form containing a later call remains a recoverable later-family boundary |
| arithmetic, bitwise, comparison, shift and pointer-to-member binary operators | final `core.Ebinop`, or template `Eunresolved_binop` only when Clang omitted the optional result and mparser's final-operand `type_of` says unresolved. C++ reproduces mparser's outer-type rules, including `Eparam` versus `Eunresolved_global`, exact `Tresult_global`, character-versus-`Tnum` reversed pointer addition, same-pointee pointer difference, and exact incompatible-pointer `Tunsupported` |
| `=`, compound assignments | final `core.Eassign` and `core.Eassign_op` with operand order then result type, or exact unresolved template syntax after the same optional-result/type-of decision |
| comma, `&&`, `||` | final `core.Ecomma`, `core.Eseqand`, `core.Eseqor`, or exact template unresolved forms according to mparser's final left-operand `type_of` test (including non-type `Eparam` and `Eunresolved_global`), with no fabricated result-type child |
| built-in array subscript | final `core.Esubscript`; array-to-pointer decay is erased before building operands, and template `infer_subscript` is evaluated in C++ (including its synthetic pointer `Cl2r` and rejection of a non-type `Eparam` as an index) rather than guessed from Clang's recursively dependent result type |
| `sizeof`/`alignof` type or expression | final `core.Esizeof`/`core.Ealignof` with `inl type` or `inr expression`, followed by result type |
| preferred alignment | parser helper evaluated to final `Eunsupported "alignof_preferred" result_type` |
| `SizeOfPackExpr` | final `Eint length result_type`, or template `Eunresolved_sizeof_pack name result_type` |
| `ChooseExpr` and other unhandled expression subclasses | completed by the exact general unsupported lowering in family 7 below; no fake recursive syntax is emitted |

## 4B.1 family 3 — calls and members

| Legacy/Clang family | Owned final IR disposition |
|---|---|
| ordinary `CallExpr` | final `core.Ecall callee args`; children are callee then arguments in source order, including nested zero/two-argument calls |
| dependent `CallExpr` | eager mparser expansion to `core.Eunresolved_call name args`; function/global/local and dependent-member callees become the exact final name, including synthesized `Nlocal`, `Tresult_unop`, and `Tresult_member` structures. `UnresolvedMemberExpr` overload sets preserve legacy's exact `Nunsupported "Eunsupported: UnresolvedMemberExpr"`, non-name-preserving cast descriptors preserve exact `Nunsupported "Ecast"`, and array-subscript callees first reproduce `infer_subscript` before becoming exact `Nunsupported "Esubscript"` or `Nunsupported "Eunresolved_binop"` |
| pseudo-destructor call | the `CallExpr` level is erased into final `Epseudo_destructor arrow destroyed_type base`; the root keeps direct pseudo-destructor provenance and appends transformed call provenance |
| `CXXOperatorCallExpr` | final `core.Eoperator_call` with `operator_impl.Func` or `operator_impl.MFunc`; recursive order is name, function type, then Clang's complete argument list, with exact Static/Virtual/Direct dispatch |
| allocation/deallocation overloaded-operator calls | completed in family 5 below with structured `OONew`/`OODelete` array flags; no fake scalar encoding is accepted |
| field `MemberExpr` | eager parser expansion to `core.Emember arrow base field_atomic mutable field_type`; booleans are scalar and recursive order is base, field, type |
| enum/static data/static method `MemberExpr` | eager parser expansion to `core.Emember_ignore arrow base synthesized_result`, where the result is exact `Eenum_const` or `Eglobal` |
| `CXXDependentScopeMemberExpr` | final `core.Eunresolved_member object name`; arrow access synthesizes `Eunresolved_unop Rarrow base` without a syntax-only location level |
| direct/virtual `CXXMemberCallExpr` | final `core.Emember_call arrow (inl (name, dispatch, function_type)) object args`; recursive order is name, type, object, arguments |
| `.*`/`->*` member-pointer call | final `core.Emember_call arrow (inr member_pointer_expr) object args`; recursive order is member pointer, object, arguments |
| unary address of non-static field/method | final `Eglobal_member name declaration_type`, not `Eaddrof (Eglobal ...)` |
| ordinary `CXXThisExpr` | final `Ethis expression_type`; implicit-object field and method calls retain it as the first object subtree |
| lambda `this`/captured variables | completed in family 6 below through eager capture-field and qualifier expansion |
| `CXXDefaultArgExpr` | final `Eimplicit argument` with an implicit origin derived from the argument; it is not erased |
| direct `CXXPseudoDestructorExpr` | final three-argument `Epseudo_destructor arrow destroyed_type base`; the call-wrapped route above is independently covered |

## 4B.1 family 4 — construction and initialization

| Legacy/Clang family | Owned final IR disposition |
|---|---|
| `CXXConstructExpr`/`CXXTemporaryObjectExpr` | final `Econstructor name arguments type`; recursive order is name, every Clang argument (including `Eimplicit` defaults), then result type |
| `CXXInheritedCtorInitExpr` | final `Einherited_constructor name [localname.anon 0; …] type`; anonymous identifiers are scalar list elements, so recursive children are only name then type. The compiler-generated root is implicit and derives from its written inherited-constructor range |
| `ParenListExpr` | Static mode preserves exact `Eunsupported "ParenListExpr" Tauto`; Template mode emits final `Eunresolved_parenlist optional_type expressions`, with no parser-only level |
| `CXXUnresolvedConstructExpr` | exact legacy `Eunsupported "CXXUnresolvedConstructExpr" declaration_type`; no constructor semantics are guessed |
| transparent `InitListExpr` | erased clone of its sole semantic initializer with an appended transformed range; no location-tree level |
| void/dependent `InitListExpr` | final `Eunresolved_initlist None expressions`, with no result-type child |
| union/ordinary/array `InitListExpr` | final `Einitlist_union field optional_initializer type` or `Einitlist initializers optional_filler type`; array filler is rebuilt as one distinct option occurrence after explicit inits |
| `ExprWithCleanups` | retained final `Eandclean child` (not erased), with an implicit wrapper origin derived from the child |
| non-extending / scope-extending `MaterializeTemporaryExpr` | final `Ematerialize_temp child value_category`, or exact legacy `Eunsupported "MaterializeTemporaryExpr" declaration_type` for scope extrusion; both roots are implicit and derived |
| `ImplicitValueInitExpr` / `CXXScalarValueInitExpr` | final `Eimplicit_init type`; compiler-inserted array fillers are implicit, while written scalar `T()` syntax is explicit |
| `ArrayInitLoopExpr` / `ArrayInitIndexExpr` / scoped `OpaqueValueExpr` | final `Earrayloop_init`, `Earrayloop_index`, and `Eopaque_ref` with exact fresh opaque indices, nested levels, array size, and child order. Generated source/init subtrees are implicit and derive from the loop occurrence |
| `CXXBindTemporaryExpr` / `CXXDefaultInitExpr` | erased clone of the semantic child with transformed provenance, as required by the legacy identity behavior |

## 4B.1 family 5 — allocation and deallocation

| Legacy/Clang family | Owned final IR disposition |
|---|---|
| resolved `CXXNewExpr` | final `Enew (operator_name, function_type) placement_args new_form allocated_type array_size initializer`; recursive order is name, function type, placements, allocated type, optional size, optional initializer. The allocated type prefers written `TypeLoc` |
| allocating/aligned new | structured scalar `new_form.Allocating passAlignment`; aligned and ordinary forms share the same recursive shape |
| reserved global placement new | exact scalar `new_form.NonAllocating`; checked construction requires exactly one placement argument and forbids passed alignment |
| dependent `CXXNewExpr` without an operator | exact legacy `Eunsupported "CXXNewExpr" declaration_type`, never a fabricated allocation function |
| resolved `CXXDeleteExpr` | final `Edelete isArray operator_name argument destroyed_type`; recursive order is name, argument, inferred type |
| unresolved template `CXXDeleteExpr` | mparser's helper is evaluated eagerly to final `Eunsupported "unresolved delete" Tvoid`; its array flag and argument are erased and create no final location children. The same AST in Static mode is rejected rather than fabricated |
| allocation/deallocation `CXXOperatorCallExpr` | final `core.Eoperator_call (OONew/OODelete isArray) (operator_impl.Func/MFunc …) arguments`; operation array flags and implementation products are structured, checked containers with no location levels |

## 4B.1 family 6 — lambdas, captures, atomics, and `va_arg`

| Legacy/Clang family | Owned final IR disposition |
|---|---|
| `LambdaExpr` in Static mode | final `Elambda closure_name capture_initializers`; capture initializers retain source order and are evaluated in the enclosing declaration context. A stack of initializing closures skips only the closure being initialized, preserving an outer mutable/qualified lambda context for nested lambdas |
| `LambdaExpr` in Template mode | final `Elambda closure_name capture_initializers`; mparser's `Einitializing_type` helper is evaluated eagerly, so unresolved paren/init lists directly carry `Some capture_field_type`; nested capture initializers preserve the outer template closure context |
| captured-variable `DeclRefExpr` | eager `Ecapture_var` expansion to final `core.Emember true (Ethis closure_pointer_type) field false field_type`; closure cv qualification, by-value/by-reference field type, and recursive order are exact |
| captured `CXXThisExpr` | eager `Ecapture_this` expansion to final `Ecast Cl2r (core.Emember true (Ethis closure_pointer_type) ".this" false capture_field_type)`; generated helper nodes are synthesized and anchored to the written `this` |
| unevaluated enclosing-variable reference | eager `Eunevaluated_var` expansion to exact final `Eunsupported "Unevaluated variable: name" (Tref declaration_type)` with no capture-field fabrication |
| `AtomicExpr` | final `Eatomic operation subexpressions result_type`; operation spelling comes from the shared Clang-version backport and children are every Clang subexpression followed by type |
| `VAArgExpr` | final `Eva_arg argument result_type`; parser-only type decay spelling is already evaluated to the final core type |
| VLA lambda capture | lowered without dereferencing Clang's null initializer. Static mode preserves the legacy explicit `Eunsupported "empty expression (nullptr)" Tauto` capture followed by the actual array capture. Template mode preserves `"variable length array capture"`, finalizes the legacy printer's missing required type argument as `Tauto`, and eagerly reduces the remaining `Einitializing_type` captures. The compiler-generated unsupported capture has an implicit origin directly anchored to the lambda; its generated `Tauto` child is synthesized and anchored to that implicit occurrence |

## 4B.1 family 7 — conditionals, `offsetof`, concepts, and unsupported forms

| Legacy/Clang family | Owned final IR disposition |
|---|---|
| `ConditionalOperator` | final `Eif condition true false declaration_type`; recursive order is the three expressions followed by type |
| GNU `BinaryConditionalOperator` | final `Eif2 opaque_index common condition true false declaration_type`; every `OpaqueValueExpr` becomes an implicit `Eopaque_ref` with a deterministic expression-scope index and synthesized/implicit origin anchored to the written conditional. Nested GNU conditionals allocate outer-before-inner indices exactly like legacy |
| supported field `OffsetOfExpr` | final `Eoffsetof parent_record_type field_identifier result_type`; the field identifier is the constructor's scalar `ident`, while recursive children are parent and result types |
| unsupported multi-component `OffsetOfExpr` | exact final `Eunsupported "OffsetOfExpr" result_type`; custom warning text is not part of the semantic term |
| `ConceptSpecializationExpr` | parser helper evaluated eagerly: Template-dependent form is exact `Eunsupported "potentially dependent concept specialization" type`; Static dependent form is `Ebool`; nondependent form follows the legacy helper's exact `Eunsupported "unresolved concept specialization" Tbool`, with generated `Tbool` anchored to the written occurrence and the erased concept name absent from children |
| `ChooseExpr`, `CXXThrowExpr`, `CXXTypeidExpr`, `RecoveryExpr`, and every other expression subclass without a dedicated legacy visitor | exact final `Eunsupported StmtClassName declaration_type`, matching `loc::describe(Stmt)`; operands are not recursed into and no opaque fallback term is used |
| GNU `StmtExpr` | final `Estmt statement declaration_type`; the compound statement is lowered through `BuildStmt`, and recursive order is statement then type |

## 4B.2 — local declarations and statements

| Legacy/Clang family | Owned final IR disposition |
|---|---|
| ordinary/static/external local `VarDecl` | final `Dvar` or `Dinit`, or explicit zero-cardinality filtering for external storage. Template `Dvar` eagerly reduces `mparser.Dvar` so an initializer directly carries its final initializing type |
| type/static-assert/function local declaration | explicit zero-cardinality result; a containing `Sdecl` remains written but has no phantom declaration children |
| `DecompositionDecl`/`BindingDecl` | final `Ddecompose` with initializer before source-ordered `Bvar`/`Bbind`; anonymous local names are scoped per decomposition and scalar-only |
| loops, if/switch/case/default, expressions, returns, compounds, nulls | final core statement nodes. Case/default return several siblings for list splicing; missing else and noncompound-switch wrappers are anchored synthesized `Sseq` nodes |
| range-for | parser `Sforeach` is evaluated eagerly into final optional-init/range/begin/end/`Sfor` order and a generated inner `Sseq`; dependent forms retain exact `Sunsupported "dependent for-each loop"` |
| GNU asm, attributes, labels/goto, try | final structured core nodes with exact scalar payloads and recursive expression/substatement order; try is exact `Sunsupported "try"` |
| unknown non-null statement class | remains a recoverable builder error rather than an invented fallback, matching the legacy fatal boundary |
| `if consteval` | final `Sif_consteval`; an omitted else is an anchored synthesized empty `Sseq`, exercised under C++23 |

## Checked evidence

- `tests/type_expr_builder_cram/type_expr_builder.t` independently prints the
  same selected expressions through legacy `ClangPrinter`/`CoqPrinter`, then
  proves exact Rocq equality for every selected static/template cast, literal,
  operator, trait, dependent-pointer, non-type-parameter, dependent-global,
  ordinary/dependent call, member, member-call, operator-call, `this`,
  pseudo-destructor, constructor, inherited-constructor, paren/init-list,
  cleanup/materialization, implicit-init, array-loop, allocating/aligned/
  placement new, resolved/unresolved delete, dependent-new, static/template
  lambda, by-value/by-reference/`this`/unevaluated capture, nested mutable
  outer-lambda capture initializer, atomic, `va_arg`, ordinary/GNU/nested
  conditional, opaque reference, supported/unsupported `offsetof`, general
  unsupported form, and C++20 concept term under C++17 and C++20 as applicable.
- `tests/unit/TypeExprBuilderProbe.cpp` checks implicit/explicit/inherited,
  synthesized, and transformed origins; exact cast/type/operand child order;
  complete representative operator and call/member shapes; overloaded and
  explicit-template unresolved member callees; name-preserving versus
  non-name-preserving explicit callee casts; nearest-first erased-callee
  wrapper ranges; constructor/default-argument and init-list child order;
  implicit/transformed initialization provenance; deterministic opaque/index
  nesting; allocation child order and written allocated-type provenance;
  mparser-generated type origins; member-address lowering; dependent mode;
  lambda helper reduction and synthesized capture provenance; nested outer
  closure cv/field-type/context retention; supported Static/Template VLA
  capture shape and implicit/synthesized anchor chain; atomic/`va_arg` child shape;
  conditional/opaque deterministic index and anchor shape; `offsetof` order;
  concept helper reduction; final statement-expression shape; local
  zero/one cardinality, binding kinds, statement sibling splicing, synthetic
  missing-else/switch/range origins, C++23 consteval-if, unknown-statement
  rejection, selection validation, and determinism.
- `tests/unit/IRTests.cpp` checks final rendering/grouping for character,
  multi-code-unit string, float bits, explicit/path/unsupported casts,
  `Tresult_global`/`Tresult_unop`/`Tresult_member`,
  supported/unsupported/unresolved unary forms, every binary and compound
  operation domain, traits, every call/member, construction/initialization,
  allocation product/sum/list/option grouping, lambda/atomic/`va_arg`,
  conditional/GNU-conditional, and `offsetof` rendering and shape, exact
  flattened child order, and malformed factory rejection.
