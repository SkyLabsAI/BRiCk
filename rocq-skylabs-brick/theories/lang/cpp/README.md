C++ Semantics
==

This directory contains an (axiomatic) semantics for the parse trees described in `Cpp.Syntax`.
To avoid introducing closed world assumptions, the semantics is defined using a combination of `Parameter`s and `Axiom`s.

## Syntax
The [syntax](syntax) directory contains a deep embeddding of the syntax tree based on Clang.

- [names.v](syntax/names.v) contains the syntax of (mangled) names
- [types.v](syntax/types.v) contains the syntax of types
- [expr.v](syntax/expr.v) contains the syntax of expressions
- [stmt.v](syntax/stmt.v) contains the syntax of statements
- [translation_units.v](syntax/translation_units.v) contains the syntax of translation units, i.e. a `.cpp` file.
- [typing.v](syntax/typing.v) contains definitions related to types.

## Semantics
The [semantics](semantics) directory contains definitions pertaining to values and
primitive operators.

- [values.v](semantics/values.v) contains a notion of values, address arithmetic, etc.
- [sub_module.v](semantics/sub_module.v) contains definitions related to compatibility of compilation units, used for supporting `#include` files
- [operator.v](semantics/operator.v) contains definitions of primitive operators.
- [intensional.v](semantics/intensional.v) contains some definitions used for dealing with intensional parts of our AST
- [subtyping.v](semantics/subtyping.v) defines the sub-typing relation.
- [dispatch.v](semantics/dispatch.v) defines the semantics of virtual function resolution.


## Logic
The [logic](logic) directory contains axiomatic semantics for C++.

- [logic/pred.v](logic/pred.v) declares our ambient logic using Iris
- [logic/simple_pred.v](logic/simple_pred.v) instantiates our logic.
- [logic/path_pred.v](logic/path_pred.v) defines a logic over paths, e.g. field access, array subscript, etc
- [logic/heap_pred.v](logic/heap_pred.v) defines various assertions over the heap for primitive data types
- [logic/wp.v](logic/wp.v) declares the set of weakest pre-condition assertions
- [logic/expr.v](logic/expr.v) defines the axiomatic semantics of expressions
- [logic/stmt.v](logic/stmt.v) defines the axiomatic semantics of statements
- [logic/call.v](logic/call.v) defines the rule for argument evaluation
- [logic/initializers.v](logic/initializers.v) defines the rules of initialization
- [logic/destructors.v](logic/destructors.v) defines the rules of de-initialization lists
- [logic/destroy.v](logic/destroy.v) defines the rules for destructing objects, e.g. calling destructors on primitives, objects, and arrays.
- [logic/spec.v](logic/spec.v) defines a Hoare logic style for representing function specifications.
- [logic/func.v](logic/func.v) defines axiomatic semantics for functions, methods, constructors, and destructors
- [logic/atomics.v](logic/atomics.v) defines the semantics of primitive atomic operations such as fetch-and-add, etc.
- [logic/layout.v](logic/layout.v) defines the semantics of `struct`, `union`, and `array` layout.


## Compilation Axioms
The [compile.v](compile.v) file contains the axioms about compilation linking `fspec` and `wp_func`/`wp_method`/`wp_ctor`/`wp_dtor` (defined in [logic/func.v](logic/func.v)).

## cpp2v Integration
The [parser.v](parser.v) file sets up the environment needed for compiling the results of `cpp2v`.

## Notations
A collection of notations live in following files:
- [primitives.v](primitives.v) contains notations such as `intR`, `shortR`, etc. for primitives.
- [heap_notations.v](heap_notations.v) defines some short-hand used for writing logic assertions, e.g. `p |-> r`, `p ., f |-> r`, etc.
- [spec_notations.v](spec_notations.v) defines combinators for building Hoare logic-style specifications (defined in [logic/spec.v](logic/spec.v))
