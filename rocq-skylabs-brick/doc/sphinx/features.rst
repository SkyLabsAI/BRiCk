.. _features:

#################
Language Support
#################

The |project| program logic is aimed to be a formalization of pragmatic C++. Its feature set is guided by the requirements of low-level program verification and also some pragmatic considerations.

Status
======

This page describes |project| and ``cpp2v`` as of October 2026. Each entry links to its tracking issue where one exists. The
:file:`CHANGES.md` file at the repository root lists breaking changes.

A C++ construct that |project| does not fully support falls into one of the
following categories, from most to least disruptive:

Rejected by ``cpp2v``
  ``cpp2v`` stops with a fatal error. No part of the translation unit can be
  verified.

Unsupported declaration
  ``cpp2v`` emits ``Dunsupported`` for a type and continues. Functions whose
  code needs that type cannot be verified; other functions in the
  translation unit are unaffected.

Opaque record
  ``cpp2v`` emits ``Dopaque`` for a record whose body it cannot model, keeping
  its size, alignment, destructor, and :cpp:`operator delete`. Code that only
  passes, stores, or destroys objects of the type can be verified against
  specifications of its member functions; code that needs the record's
  members or bases cannot.

Unsupported syntax
  ``cpp2v`` emits ``Eunsupported``, ``Sunsupported``, ``Tunsupported``, or
  ``Bunsupported``. These have no semantics: a proof that reaches one gets
  stuck.

No semantics
  ``cpp2v`` translates the construct faithfully, but the program logic has no
  rule for it. A proof that reaches it gets stuck.

Partial
  The program logic covers the construct, but not all of its behaviors, or
  covers it with a documented restriction.

``skylabs.lang.cpp.syntax.supported`` checks a translation unit for many of
these constructs.

Unsupported Features
====================

.. list-table::
   :header-rows: 1
   :widths: 40 20 40

   * - Feature
     - Category
     - Notes
   * - Coroutines, computed :cpp:`goto` (``goto *p``), MSVC inline
       assembly, SEH (``__try``)
     - Rejected by ``cpp2v``
     - Any statement kind that ``cpp2v`` has no printer for is fatal.
   * - Bitfields
     - Opaque record
     - A record with a bit-field becomes an *opaque boundary* (``Gopaque``):
       ``cpp2v`` keeps its size, alignment, destructor, and
       :cpp:`operator delete`, but not its members or bases. Callers can own
       such an object through an abstract ``Rep``, pass it by value, and
       destroy it. Accessing its members, verifying its member functions,
       ``anyR``, changing its :cpp:`const`-ness, and :cpp:`delete` are not
       supported. Records that also have a virtual base, and C records, remain
       unsupported declarations.
       `BRiCk#307 <https://github.com/SkyLabsAI/BRiCk/issues/307>`_
   * - :cpp:`virtual` inheritance (virtual base classes)
     - Partial
     - Such a class is a ``Gvstruct``: it has a size, its fields and
       non-virtual bases have offsets, and clients can write ``Rep``\ s for
       it (``vbaseR``). Constructors and destructors can be verified, and
       complete objects created and destroyed, when no class in the
       hierarchy has a :cpp:`virtual` function and no virtual base
       overlaps the data of another subobject (overlapping padding, as
       empty virtual bases do, is fine). Conversions to or from a
       virtual base, :cpp:`virtual` dispatch, :cpp:`delete`,
       :cpp:`const` objects, and explicit destructor calls are not
       supported. This includes standard types built on it, e.g.
       :cpp:`std::basic_ostream`.
   * - Under-aligned fields or base classes (e.g. some :cpp:`[[gnu::packed]]`
       records)
     - Unsupported declaration
     - Typed pointers in |project| imply natural alignment. Packed records
       whose fields are all bytes, or whose fields are explicitly aligned,
       are supported.
   * - Template parameter packs, unresolved concept specializations
     - Unsupported syntax
     - Pack *arguments* and :cpp:`sizeof...` are supported.
   * - Variable-length arrays
     - Unsupported syntax
     - Their initialization has no semantics. The array bounds of typedefs,
       variables and function parameters of variably modified types are
       evaluated where the type is declared and must be greater than zero
       (``Dvla_bounds``). Condition variables of, and casts to, such types
       are unsupported.
       `BRiCk#59 <https://github.com/SkyLabsAI/BRiCk/issues/59>`_
   * - Exceptions: :cpp:`throw`, :cpp:`try`, :cpp:`typeid`, dynamic exception
       specifications
     - Unsupported syntax
     - |project| additionally *assumes* that function calls do not throw.
       `BRiCk#15 <https://github.com/SkyLabsAI/BRiCk/issues/15>`_
   * - Lifetime-extended temporaries, e.g. :cpp:`const T& x = f();` or
       :cpp:`std::initializer_list<int> il = {1, 2, 3};`
     - Unsupported syntax
     - These require scope-extruded temporaries.
       `BRiCk#272 <https://github.com/SkyLabsAI/BRiCk/issues/272>`_
   * - :cpp:`long double` (x87 extended precision), vector types
       (``__vector_size__``), block pointers
     - Unsupported syntax
     -
   * - Unknown cast kinds, non-default calling conventions
     - Unsupported syntax
     -
   * - :cpp:`goto` backward, into a nested statement, or past a
       declaration (even a vacuously initialized one)
     - No semantics
     - Forward :cpp:`goto` to a later statement of the same or an enclosing
       block is supported (``Kblock`` in ``logic/stmt.v``); other jumps reach
       the function boundary as ``Goto l``, which is ``False``.
       `BRiCk#515 <https://github.com/SkyLabsAI/BRiCk/issues/515>`_
   * - :cpp:`if consteval`
     - No semantics
     -
   * - GCC inline assembly (:cpp:`asm`)
     - No semantics
     - See :ref:`machine-interop` for the supported interface to assembly.
   * - Defining variadic functions (:cpp:`va_arg`)
     - No semantics
     - *Calling* variadic functions, e.g. :cpp:`printf`, is supported.
   * - GNU statement expressions (``({ ... })``)
     - No semantics
     -
   * - :cpp:`offsetof`
     - No semantics
     - Single-field :cpp:`offsetof` is translated but has no rule; other forms
       (nested members, array elements, bases) are unsupported syntax.
   * - :cpp:`dynamic_cast`
     - No semantics
     -
   * - :cpp:`reinterpret_cast`
     - No semantics
     - `BRiCk#156 <https://github.com/SkyLabsAI/BRiCk/issues/156>`_
   * - Member pointer operators (:cpp:`.*`, :cpp:`->*`) and calls through
       member function pointers
     - No semantics
     - Member pointer *types* have a layout, and null member pointers can be
       created. Default-initializing a member pointer is an error.
   * - Explicitly defaulted constructors and methods that ``cpp2v`` does not
       elaborate
     - No semantics
     - Implicit and defaulted members that Clang elaborates are supported.
   * - Initializing members of anonymous structs or unions in a constructor
       initializer list; indirect or self initialization of unions
     - No semantics
     -
   * - Destroying :cpp:`operator delete`
     - No semantics
     -
   * - Default arguments of reference type
     - No semantics
     - `BRiCk#390 <https://github.com/SkyLabsAI/BRiCk/issues/390>`_
   * - Function-local :cpp:`static` variables
     - Partial
     - The rules for the initialization guard exist, but nothing provides the
       initial ``static_initialized`` ownership, so first use gets stuck.
   * - Changing the active member of a :cpp:`union`
     - Partial
     - The ``union_change`` rule is disabled pending a sound formulation as
       part of assignment. Implicit union copies translate to an empty body.
       `BRiCk#345 <https://github.com/SkyLabsAI/BRiCk/issues/345>`_
   * - Implicit copy assignment of byte arrays
     - Partial
     - Gets stuck at :cpp:`__builtin_memcpy`. `BRiCk#369 <https://github.com/SkyLabsAI/BRiCk/issues/369>`_
   * - Zero-initialization
     - Partial
     - Only trivial cases are supported. `BRiCk#135 <https://github.com/SkyLabsAI/BRiCk/issues/135>`_
   * - :cpp:`volatile`
     - Partial
     - :cpp:`volatile` qualifiers are ignored. Default-initialization of a
       :cpp:`volatile` object is unsupported.
   * - :cpp:`switch`
     - Partial
     - Mixing :cpp:`switch` with other control flow (e.g. Duff's device) is
       not supported.
   * - Atomics
     - Partial
     - All atomic accesses must be sequentially consistent [#weak-mem]_.
       Compare-exchange is supported on integers, not pointers.
   * - :cpp:`template` code
     - Partial
     - Templates can only be reasoned about *after* instantiation to specific
       arguments.
   * - Translation unit initialization (initialization of globals)
     - Partial
     - Not covered by the program logic.
   * - Flexible array members, `transparent replacement
       <https://eel.is/c++draft/basic.life#8>`_
     - Not supported
     - Flexible array members are not standard C++ but are common in
       practice.

Floating point arithmetic and comparisons are supported for IEEE-754 formats
(half, single, double, and quad precision), with semantics given by Flocq.
x87 :cpp:`long double` values are abstract.

Soundness Caveats
=================

The following are known ways in which a proof can be weaker than it appears.

* **Exceptions.** Function calls are assumed not to throw.
* **Member functions** are modeled as functions. Exploiting this requires
  :cpp:`reinterpret_cast`.
* **Defaulted functions.** |project| relies on the semantics of defaulted
  functions (default constructors, assignment operators, etc.) as generated by
  Clang. A different compiler may generate different, still correct, code
  that invalidates your proof.

Other known soundness bugs, and the pull requests that fix them, carry the
`soundness label <https://github.com/SkyLabsAI/BRiCk/issues?q=is%3Aopen+label%3Asoundness>`_.

Trusted Base
------------

The program logic is stated axiomatically: ``rocq-skylabs-brick/theories``
contains about 450 ``Axiom`` declarations. The models under
``theories/lang/cpp/model`` currently contain 8 ``Admitted`` lemmas
(``simple_pred.v``, ``inductive_pointers.v``, ``inductive_pointers2.v``).

Deviations from the Standard
============================

In certain instances, |project|'s semantics deviates from the C++ standard.

* |project|'s semantics do not currently permit "pointer zapping". See :ref:`no-pointer-zapping`.
* |project| uses `Tnum sz sgn` to represent all integer types rather than the standard types :cpp:`char`, :cpp:`short`, :cpp:`int`, :cpp:`long`, :cpp:`long long`.
* |project| is based on the Clang front-end IR. We believe that this is a reasonable proxy for source-level C++.
* The |project| program logic *assumes* that the abstract syntax tree is well-typed and uses this assumption to avoid performing type checking within the semantics. If you are using `cpp2v` to generate the AST, then Clang will ensure that the syntax tree is well typed.

Toolchain Requirements
======================

* ``cpp2v`` requires LLVM 20 through 22 (as tested in CI). The release images
  use LLVM 22.
* Generate the AST with exactly the same Clang flags and target as your build.
  The AST fixes implementation-defined behavior, such as the sizes of integer
  types (whether incrementing a :cpp:`long` holding ``0x7fffffff`` overflows),
  and the code Clang generates for defaulted functions.

Extensions to the Standard
===========================

|project| also extends the C++ standard in limited ways to make low-level program verification possible.
For example, inter-operation with assembly (see :ref:`machine-interop`), sharing data across address spaces, etc.
We believe that our extensions are conservative and characterize the way that low-level programmers rely on compilers to work.

.. [#weak-mem] We plan to support weak memory C++ in the future based on other work in Iris.
