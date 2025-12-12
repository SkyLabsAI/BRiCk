.. _object_layout:

#############################################################
Object representation, layout and padding
#############################################################

This document highlights some tricky aspects around object
representation, layout and padding in C++ and describes how |project| deals with them.

A basic problem when formalizing C(++) is that there are multiple ways to view the same
data [#krebbers-thesis-2.5]_:

- In a *high-level* way using arrays, structs and unions.
- In a *low-level* way using unstructured and untyped byte representations.

This especially affects reasoning about the representation of an object in memory, i.e.
how its data is laid out, especially data like padding which is part of the low-level presentation
but *not* part of the high-level representation.

.. warning::

  Much of the reasoning described in this section is still experimental and subject to change.
  In practice, many C++ programs do not require this level of reasoning.

.. _object_layout.values:

Representing Values
====================

.. The C++ standard `talks explicitly about when materialization occurs <https://eel.is/c++draft/class.temporary#2>`_.

In the |project| separation logic, we choose to immediately materialize all aggregates (i.e. aggregates do not have a Coq-value representation), and address the delayed materialization through the fact that not all pointers (|link:bluerock.lang.cpp.semantics.ptrs#PTRS.ptr|) are required to be backed by memory.

Representing Values in Memory
-----------------------------------

Given that we materialize all aggregates, we can provide a simple characterization of the different types of Coq values (|link:bluerock.lang.cpp.semantics.values#VAL_MIXIN.val|) which model C++ values; all values are one of:

- |link:bluerock.lang.cpp.semantics.values#VAL_MIXIN.Vptr| - for C++ pointer and reference values
- |link:bluerock.lang.cpp.semantics.values#VAL_MIXIN.Vint| - for C++ integral values (excluding floating-point values)
- |link:bluerock.lang.cpp.semantics.values#VAL_MIXIN.Vraw| - for the low-level representation of C++ objects; refer to :ref:`this section <object_layout.axiomatized_object_model>` for more details
- |link:bluerock.lang.cpp.semantics.values#VAL_MIXIN.Vundef| - for uninitialized values, upon which all operations yield :ref:`Undefined Behavior <undefined_behavior>`

This characterization enables us to use a single abstraction to model the in-memory representation of C++ values - called |link:bluerock.lang.cpp.logic.heap_pred#primR| `: type -> Qp -> val -> Rep` - which reflects the fractional ownership (`Qp`\ ) of some Coq-model `val`\ ue of a given C++ `type`.
`Rep ~= ptr -> mpred` models the location agnostic in-memory representation of some resource, and for any given `p : ptr` and `R : Rep`\ , `p |-> R` reflects the materialization of the resource modeled by `R` at the logical pointer `p`.

.. _object_layout.arrays:

Reasoning about the layout of an array in memory
=================================================

The C++ standard defines the `layout of arrays <http://eel.is/c++draft/dcl.array#6>`_ as
follows:

.. pull-quote::

  An object of type “array of N U” contains a contiguously allocated non-empty set of N
  subobjects of type U, known as the elements of the array, and numbered 0 to N-1.

This means that there is no padding between elements of an array.

How is this reflected in |project|?
-------------------------------------

The `Axiom` |link:bluerock.lang.cpp.semantics.ptrs#PTRS.eval_o_sub| is defined to compute the the numerical
offset needed to subscript into an array based on the size of the underlying type and the index which
is being used for the subscript. Furthermore, none of the definitions and the related theories of
arrays contained within |link:bluerock.lang.cpp.logic.arr| mention padding in any capacity.

.. _object_layout.structs:

Reasoning about the layout of a struct in memory
=================================================

Reasoning about the layout of an object in memory is often required when interacting with drivers.
For example, consider the following code:

.. code-block:: cpp

  void *dma_address = ...;
  struct dma_struct {
    uint64 a;
    uint64 b;
  };

  void do_dma() {
    struct dma_struct *ptr = dma_address;
    // This example ignores many concerns including:
    // - UB via data-races
    // - the compiler reordering writes
    // - endianness
    // - alignment
    ptr->a = ...; // (1) This write must go to dma_address + 0
    ptr->b = ...; // (2) This write must go to dma_address + 8
  }

This code communicates with a device via DMA by casting a pointer to a :cpp:`struct` and then uses field accesses to write to memory.
The important point is that the writes on line `(1)` and `(2)`, must go to the address `dma_address + 0` resp. `dma_address + 8` for correctness.
In particular, there must not be padding at the start of the :cpp:`struct` and between `a` and `b`.

*How can this reasoning be justified?* The C++ standard itself only gives light
guarantees about the `layout of structs <http://eel.is/c++draft/class.mem#26>`_:

.. pull-quote::

   If a standard-layout class object has any non-static data members, its address is
   the same as the address of its first non-static data member if that member is not
   a bit-field.
   Its address is also the same as the address of each of its base class subobjects.
   [Note: There might therefore be unnamed padding within a standard-layout struct
   object inserted by an implementation, but not at its beginning, as necessary to
   achieve appropriate alignment. — end note]

.. note::

   A standard-layout class object has non-static data members **xor** base classes (c.f. `this set of examples <https://eel.is/c++draft/class.prop#4>`_ from the standard).

Thus, the C++ standard guarantees that the write on line `(1)` goes to  `dma_address + 0`,
but on its own it does not guarantee the exclusion of padding between `a` and `b`.
However, more concrete guarantees are given by the platform ABI and we rely on those for
the particular architectures which we support. For example, the ARM ABI [#abi-arm]_
guarantees that:

.. pull-quote::

   - The alignment of an aggregate shall be the alignment of its most-aligned component.
   - The size of an aggregate shall be the smallest multiple of its alignment that is
     sufficient to hold all of its members when they are laid out according to these rules.

.. note::

   We also make an **additional assumption**: For :ref:`Plain Old Data (POD) <object_layout.concepts.pod>`,
   compilers only insert padding between fields if it is necessary to achieve alignment.

How is this reflected in |project|?
------------------------------------

The address offset of a |link:bluerock.lang.cpp.semantics.ptrs#PTRS.offset| is determined by |link:bluerock.lang.cpp.semantics.ptrs#PTRS.eval_offset|.
|project| currently supports reasoning about the layout of (a limited number of) aggregates by embedding the layout information from the Clang front-end into the |project| abstract syntax tree (see |link:bluerock.lang.cpp.syntax.translation_unit#Struct| and |link:bluerock.lang.cpp.syntax.translation_unit#Union|\ ).

In particular, |link:bluerock.lang.cpp.logic.layout#struct_def| uses the information from the Clang front-end to enumerate the properly-|link:bluerock.lang.cpp.semantics.ptrs#PTRS.offset| bases and fields of a given struct.
Furthermore, |link:bluerock.lang.cpp.logic.pred#struct_padding| tracks the padding which the compiler (may have) inserted and |link:bluerock.lang.cpp.logic.pred#mdc_path| tracks the most derived class for objects which have a vtable.
|link:bluerock.lang.cpp.logic.layout#anyR_struct| enables the "shattering" of a (potentially uninitialized) struct into its (potentially uninitialized) constitutent pieces (as well as its |link:bluerock.lang.cpp.logic.pred#struct_padding| and |link:bluerock.lang.cpp.logic.pred#mdc_path|, if necessary).

Because the C++ standard only requires portability of the layout of certain types of aggregates, we limit the use of this information in our axioms to POD and standard layout classes (see |link:bluerock.lang.cpp.semantics.ptrs#PTRS.eval_o_field|\ ).

.. note::

   We believe that a good, platform independent way to reason about layout information is to use a combination of :cpp:`static_assert` and :cpp:`offsetof`.
   |project| does not currently support this level of reasoning about :cpp:`offsetof`, but it is likely to be added in the future by connecting |link:bluerock.lang.cpp.semantics.ptrs#PTRS.eval_offset| to the semantics of :cpp:`offsetof`.

.. _object_layout.unions:

Reasoning about the layout of a union in memory
==========================================================================================

The C++ standard defines the `layout of unions <http://eel.is/c++draft/class.union#3>`_ as follows:

.. pull-quote::

   The size of a union is sufficient to contain the largest of its
   non-static data members. Each non-static data member is allocated
   as if it were the sole member of a non-union class. [Note: A union
   object and its non-static data members are pointer-interconvertible
   ([basic.compound], [expr.static.cast]). As a consequence, all
   non-static data members of a union object have the same address. —
   end note]

.. note::

   The fact that all members "have the same address" does not mean that the same
   pointer can safely be used to access all of them. In particular, accessing
   a member which is not the **active** member of a union is UB.

How is this reflected in |project|?
------------------------------------------------------------------------------------------

The virtual address offset of a |link:bluerock.lang.cpp.semantics.ptrs#PTRS.offset| is determined by |link:bluerock.lang.cpp.semantics.ptrs#PTRS.eval_offset|.
|project| currently supports reasoning about the layout of (a limited number of) aggregates by embedding the layout information from the Clang front-end into the |project| abstract syntax tree (see |link:bluerock.lang.cpp.syntax.translation_unit#Struct| and |link:bluerock.lang.cpp.syntax.translation_unit#Union|\ ).

In particular, |link:bluerock.lang.cpp.logic.layout#union_def| uses the information from the Clang front-end to provide a disjunction of all of the properly-|link:bluerock.lang.cpp.semantics.ptrs#PTRS.offset| fields of a given union.
Furthermore, |link:bluerock.lang.cpp.logic.pred#union_padding| tracks the padding which the compiler (may have) inserted *as well as* an identifier which reflects the **active member**.
|link:bluerock.lang.cpp.logic.layout#anyR_union| enables "translating between" different members of the union.

Because the C++ standard only requires portability of the layout of certain types of aggregates we limit the use of this information in our axioms to POD and standard layout classes (see |link:bluerock.lang.cpp.semantics.ptrs#PTRS.eval_o_field|\ ).

.. note::

  |project| does not reflect that all members of the same union have the same address.
  |link:bluerock.lang.cpp.logic.layout#union_def| uses |link:bluerock.lang.cpp.semantics.ptrs#PTRS_MIXIN._field| which itself uses |link:bluerock.lang.cpp.semantics.types#offset_of|; |link:bluerock.lang.cpp.semantics.types#offset_of| uses opaque offset information from the translation unit.

  If provers require this level of reasoning in the future we could provide additional assumptions regarding the offset information contained within a given translation unit.

.. _object_layout.implicit_destruction:

Implicit Destruction
==========================================================================================

A :ref:`Trivially Destructible Object <object_layout.concepts.trivially_destructible>` supports **Implicit Destruction** - in which the compiler reclaims the underlying storage of the object *without* running any code.
The following axioms reflect the current support for **Implicit Destruction** in |project|; please refer to :ref:`this section <object_layout.axiomatized_object_model>` for more details regarding our axiomatization of the C++ memory model:

- Scalars (based on |link:bluerock.lang.cpp.logic.layout#implicit_destruct_ty|)

  * |link:bluerock.lang.cpp.logic.layout#implicit_destruct_int|
  * |link:bluerock.lang.cpp.logic.layout#implicit_destruct_bool|
  * |link:bluerock.lang.cpp.logic.layout#implicit_destruct_nullptr|
  * |link:bluerock.lang.cpp.logic.layout#implicit_destruct_ptr|
  * |link:bluerock.lang.cpp.logic.layout#implicit_destruct_member_pointer|
- Aggregates (based on |link:bluerock.lang.cpp.logic.layout#struct_def| and |link:bluerock.lang.cpp.logic.layout#union_def|, which are discussed in the :ref:`struct <object_layout.structs>` and :ref:`union <object_layout.unions>` sections above)

  * |link:bluerock.lang.cpp.logic.layout#implicit_destruct_struct|
  * |link:bluerock.lang.cpp.logic.layout#implicit_destruct_union|

.. note::

   We do not axiomatize **Implicit Destruction** for arrays of :ref:`Trivially Destructible Objects <object_layout.concepts.trivially_destructible>` because we have yet to encounter a use case for it in our code-base.

.. _object_layout.axiomatized_object_model:

Axiomatizing C++'s Object Model
==========================================================================================

While the |project| axiomatization of C++'s object model is an ongoing research and development problem - with regards to weak memory and multi C++ Abstract Machine interaction, to name a few examples - there are some important characteristics which are relatively stable.

.. _object_layout.axiomatized_object_model.high_level:

Working with the high-level representation of objects
--------------------------------------------------------------------------------

C++ programmers are usually concerned with (live) C++ objects rather than the memory in which they are resident.
To wit, our specifications speak in terms of high-level C++ objects such as |link:bluerock.lang.cpp.logic.heap_pred#primR|.
Variable declarations (c.f. |link:bluerock.lang.cpp.logic.stmt#wp_decl_var|\ ) similarly yield high-level C++ objects (which our axiomatization directly reclaims when they go out of scope).

However, the C++ Abstract Machine manages memory in which there are no resident (live) C++ objects.
Implementers of custom allocators will also need a way to reason about chunks of memory in which there are no resident (live) C++ objects.
Therefore we define |link:bluerock.lang.cpp.logic.heap_pred#blockR| (c.f. |link:bluerock.lang.cpp.logic.heap_pred#blockR_def|\ ) and axiomatize |link:bluerock.lang.cpp.logic.pred#provides_storage|.
This enables us to talk about (untyped) memory which is managed by the C++ Abstract Machine **and** to relate high-level C++ objects to the memory which backs them when necessary, respectively.

.. _object_layout.axiomatized_object_model.high_level.blockR:

Reasoning about physical memory with `blockR` and `tblockR`
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

.. note::

   |link:bluerock.lang.cpp.logic.heap_pred#blockR_def| speaks in terms of |link:bluerock.lang.cpp.logic.heap_pred#anyR| which itself relates to |link:bluerock.lang.cpp.logic.heap_pred#primR| and |link:bluerock.lang.cpp.logic.heap_pred#uninitR| (c.f. |link:bluerock.lang.cpp.logic.heap_pred#primR_anyR|\ and |link:bluerock.lang.cpp.logic.heap_pred#uninitR_anyR|\ ).
   While `primR` models initialized C++ values of a given type, we can think of the physical memory managed by the C++ abstract machine as a bunch of character arrays, and indeed this view is sound *and* relevant when dealing with custom allocators (see :ref:`this section <object_layout.axiomatized_object_model.high_level.provides_storage>`\ ).

`blockR (sz : N) (q : Qp) : Rep` is a definition which represents fractional ownership (`Qp`) of a contiguous chunk of `sz` bytes - where each byte is either uninitialized or initialized to contain some concrete value of type `char`.
`tblockR (ty : type) (q : Qp) : Rep` is a definition which represents fractional ownership (`Qp`) of a contiguous chunk of `size_of ty` bytes (c.f. |link:bluerock.lang.cpp.semantics.types#size_of|\ ) - where each byte is either uninitialized or initialized to contain some concrete value of type `char`, and where the first byte respects `align_of ty` (c.f. |link:bluerock.lang.cpp.semantics.types#align_of|\ ).
Numerous axioms and definitions within |link:bluerock.lang.cpp.logic| make use of `blockR` and `tblockR` in order to reflect the transfer of physical memory between the C++ Abstract Machine and the executing code (although most of this is hidden from verifiers).

.. _object_layout.axiomatized_object_model.high_level.provides_storage:

Relating physical memory to the high-level object which it `provides_storage` for
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

One place in which verifiers *are* exposed to the `blockR`/\ `tblockR` definitions is when proving the correctness of custom (de)allocation functions.
In particular, reasoning about C++ dynamic memory management - as axiomatized within |link:bluerock.lang.cpp.logic.new_delete| - requires the explicit tracking of the high-level C++ object which was created *as well as* the physical memory which |link:bluerock.lang.cpp.logic.pred#provides_storage| for the high-level C++ object.

When it is used (c.f. |link:bluerock.lang.cpp.logic.new_delete#wp_prval_new|\ ), `provides_storage (storage object : ptr) (storage_type : type) : mpred` relates the physical memory associated with the logical `storage` pointer to the high-level C++ object associated with the logical `object` pointer (and of type `storage_type`).
This decoupling enables useful high-level reasoning for verifiers after allocation *while also* enabling the sound reclamation of that high-level object and the physical memory in which it resides.

.. _object_layout.axiomatized_object_model.low_level:

Working with the low-level representation of objects
--------------------------------------------------------------------------------

Consider the following code that does not exhibit undefined behavior (which can be checked using `Cerberus <https://www.cl.cam.ac.uk/~pes20/cerberus/>`_):

.. code-block:: cpp

  #include<stddef.h>

  struct S {
    short a;
    // The compiler must insert padding here to satisfy the alignment requirement of b
    int b;
  };

  void custom_memcpy(void *dest, void *src, size_t n) {
     unsigned char *d = dest, *s = src;
     for(size_t i = 0; i < n; i++) {
       *d = *s;
       d++; s++;
     }
  }

  int main() {
    struct S s1, s2;
    s1.a = 1; s1.b = 2; // Create an object using its high-level representation
    custom_memcpy(&s2, &s1, sizeof(struct S)); // Copy the low-level representation of the object (including padding)
    assert(s2.b == 2); // Access the resulting memory via the high-level representation
  }

This code is interesting because it accesses both the high-level representation and low-level representation of an object.
In particular, there are parts of memory that are not accessible via the high-level representation (the padding of :cpp:`struct S`), but that are accessible via the low-level representation.

How is this reflected in |project|?
------------------------------------

|project| provides access to the low-level view of data via the `Vraw r` value - where `r` represents a "raw byte".
|project| is parametric in this notion of raw byte, but a simple model would instantiate it with `byte | pointer fragment | poison` (i.e. |link:bluerock.lang.cpp.model.simple_pred#runtime_val'| in |link:bluerock.lang.cpp.model.simple_pred|\ ).
|link:bluerock.lang.cpp.semantics.values#RAW_BYTES|, |link:bluerock.lang.cpp.semantics.values#RAW_BYTES_VAL| and |link:bluerock.lang.cpp.semantics.values#RAW_BYTES_MIXIN| contain the various axioms and definitions which underly our notion of "raw bytes".

|link:bluerock.lang.cpp.semantics.values#RAW_BYTES_VAL.raw_bytes_of_val| and |link:bluerock.lang.cpp.semantics.values#RAW_BYTES_VAL.raw_bytes_of_struct| represent the core predicates which relate high-level C++ objects to their "raw" representations.
|link:bluerock.lang.cpp.logic.raw| uses |link:bluerock.lang.cpp.semantics.values#RAW_BYTES_VAL.raw_bytes_of_val| to expose conversions from `primR` to `rawsR` - which is itself an array of `Vraw` values.
|link:bluerock.lang.cpp.logic.layout| uses |link:bluerock.lang.cpp.semantics.values#RAW_BYTES_VAL.raw_bytes_of_struct| - and the definitions within |link:bluerock.lang.cpp.logic.raw| - to axiomatize |link:bluerock.lang.cpp.logic.layout#struct_to_raw| which allows for verifiers to convert :ref:`Plain Old Data <object_layout.concepts.pod>` structs into their low-level representation.

Therefore, the example above can be verified by first converting the struct to raw bytes using |link:bluerock.lang.cpp.logic.layout#struct_to_raw|, copying the raw bytes and then converting the raw bytes back into the struct using |link:bluerock.lang.cpp.logic.layout#struct_to_raw| once again.

Appendix: C++ Standard Concepts
================================================================================

.. _object_layout.concepts.pod:

Plain Old Data (POD) vs Standard-Layout/Trivial Data
------------------------------------------------------------------------------------------

The C++ Standard defines `Plain Old Data (POD) <https://eel.is/c++draft/depr.meta.types#:POD>`_ as:

.. pull-quote::

   [...] a class that is both a trivial class and a standard-layout class, and has no
   non-static data members of type non-POD class (or array thereof). A POD type is a scalar type,
   a POD class, an array of such a type, or a cv-qualified version of one of these types.

While this concept has been deprecated - and redefined in terms of - the more granular
:ref:`standard-layout class <object_layout.concepts.standard_layout>` and
:ref:`trivial class <object_layout.concepts.trivial>`
concepts, it is an easier-to-characterize side-condition as it is stronger than either
of the previous two concepts. Furthermore, the data which we've encountered while
reasoning explicitly about the layout of structs within `BlueRock <https://bluerock-io.github.io/formal-methods>`_
has fallen into the category of **POD**. In the future we will want to refine the
C++-concepts which we expose within the semantics and relax our axioms accordingly.

.. _object_layout.concepts.standard_layout:

Standard-Layout Data
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

The C++ Standard defines a `standard-layout class <https://eel.is/c++draft/class.prop#3>`_
in the following way:

::

  (3) A class S is a standard-layout class if it:
  (3.1) has no non-static data members of type non-standard-layout class (or array of
        such types) or reference,
  (3.2) has no virtual functions and no virtual base classes,
  (3.3) has the same access control for all non-static data members,
  (3.4) has no non-standard-layout base classes,
  (3.5) has at most one base class subobject of any given type,
  (3.6) has all non-static data members and bit-fields in the class and its base classes
        first declared in the same class, and
  (3.7) has no element of the set M(S) of types as a base class, where for any type X,
        M(X) is defined as follows.
        [Note 2: M(X) is the set of the types of all non-base-class subobjects that can be
         at a zero offset in X. — end note]
  (3.7.1) If X is a non-union class type with no non-static data members, the set M(X)
          is empty.
  (3.7.2) If X is a non-union class type with a non-static data member of type X0 that
          is either of zero size or is the first non-static data member of X (where said
          member may be an anonymous union), the set M(X) consists of X0 and the elements
          of M(X0).
  (3.7.3) If X is a union type, the set M(X) is the union of all M(Ui) and the set containing
          all Ui, where each Ui is the type of the ith non-static data member of X.
  (3.7.4) If X is an array type with element type Xe, the set M(X) consists of Xe and the
          elements of M(Xe).
  (3.7.5) If X is a non-class, non-array type, the set M(X) is empty.

.. _object_layout.concepts.trivial:

Trivial Data
++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

The C++ Standard defines a `trivial class <https://eel.is/c++draft/class.prop#2>`_
in the following way:

::

  (1) A trivially copyable class is a class:
  (1.1) that has at least one eligible copy constructor, move constructor, copy assignment
        operator, or move assignment operator ([special], [class.copy.ctor],
        [class.copy.assign]),
  (1.2) where each eligible copy constructor, move constructor, copy assignment operator,
        and move assignment operator is trivial, and
  (1.3) that has a trivial, non-deleted destructor ([class.dtor]).

  (2) A trivial class is a class that is trivially copyable and has one or more eligible
      default constructors ([class.default.ctor]), all of which are trivial.
      [Note 1: In particular, a trivially copyable or trivial class does not have virtual
       functions or virtual base classes. — end note]

.. _object_layout.concepts.trivially_destructible:

Trivially Destructible Objects
------------------------------------------------------------------------------------------

The C++ Standard defines a `trivial destructor <https://eel.is/c++draft/class.dtor#8>`_
in the following way:

::

  (8) A destructor is trivial if it is not user-provided and if:
  (8.1) the destructor is not virtual,
  (8.2) all of the direct base classes of its class have trivial destructors, and
  (8.3) for all of the non-static data members of its class that are of class type (or array thereof), each such class has a trivial destructor.
  (8) Otherwise, the destructor is non-trivial.

Scalars, :ref:`trivial data <object_layout.concepts.trivial>` which uses a trivial destructor and arrays of such objects
are known as **Trivially Destructible Objects**.

.. rubric:: Footnotes

.. [#krebbers-thesis-2.5]
   Section 2.5 of `Robbert Krebbers - The C standard formalized in Coq <https://robbertkrebbers.nl/research/thesis.pdf>`_

.. [#abi-arm]
  `Procedure Call Standard for the Arm Architecture <https://developer.arm.com/documentation/ihi0042/latest?_ga=2.60211309.1506853196.1533541889-405231439.1528186050>`_
