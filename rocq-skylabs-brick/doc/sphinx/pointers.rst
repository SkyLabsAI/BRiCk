.. _pointers-and-pointer-provenance:

###############################
Pointers and pointer provenance
###############################

.. todo:: move the background on the standard out-of-line, to be skippable by people familiar with the standard.

Surprisingly, C++ pointers are not just addresses; here we explain what they are
in the C++ standard and in |project|.

Two pointers might differ despite `representing the same address <https://eel.is/c++draft/basic.compound#def:represents_the_address>`_, depending
on how they're constructed, and C/C++ optimizers are allowed to treat them
differently.

For instance, in the following snippet `px1` and `py` are always different
pointers, even when they often have the same address. In particular, since `px1` is
created from a pointer to `x`, it cannot be used to read or write to `y`; this
is similar to the restriction we show in :ref:`undefined_behavior`.

.. code-block:: cpp

  int foo() {
    int x, y;
    int *px = &x;
    int *py = &y;
    int *px1 = px + 1;
    //...
  }

More generally, a pointer identifies the "object" to which it points, and pointer
arithmetic is only allowed to produce pointers to unrelated objects in limited circumstances.

Objects in the C++ standard
================================================

Unlike in traditional object-oriented programming jargon,
in the C++ and C standards the word "object" means an instance of some
type (not necessarily a class type). Objects include variables and what
is created by :cpp:`new` expressions. These and other cases are introduced by
`[intro.object] <https://eel.is/c++draft/intro.object>`_.

Objects form a hierarchy of complete objects and subobjects (`intro.object#2
<https://eel.is/c++draft/intro.object#2>`_):

.. pull-quote::

   Objects can contain other objects, called subobjects. A subobject can be a
   member subobject ([class.mem]), a base class subobject ([class.derived]), or
   an array element. An object that is not a subobject of any other object is
   called a complete object.

Moreover, to support custom memory allocators, C++ allows allocating a
complete object inside a character array (`intro.object#3
<https://eel.is/c++draft/intro.object#3>`_); the underlying array object is said
to *provide storage* for the new object:

.. pull-quote::

  If a complete object is created ([expr.new]) in storage associated with
  another object e of type “array of N unsigned char” or of type “array of N
  std​::​byte” ([cstddef.syn]), that array *provides storage* for the created
  object if: [...]

Objects and values
-------------------

The C++ standard also talks about `values
<https://eel.is/c++draft/basic.types.general#def:value>`_, at least for
primitive objects; during its lifetime, an object of primitive type stores a
primitive value\ [#objects-have-values]_.
The |project| semantics contains a type `val` of primitive values.

Pointers, pointer values and objects
=====================================

|project| introduces an abstract type `ptr` of *pointer values*, which models
the analogous concept in the standard\ [#std-ptr-values]_. |project| uses pointer
values to identify objects: each object has an associated pointer value, but a
pointer value might not point to an object. Specifically:

* Whenever an object `o` is created, the |project| logic creates a *pointer value*
  `p : ptr` that describes where `o` lives. This pointer value need not exist in
  the C++ program, but it always exists in the logic.
* All C++ *pointers* have an associated pointer value in `ptr`, but the latter
  might not point to an actual object.

For instance, in the following program, at line 3, we can say that the pointer
value `x_ptr` points to an integer object with value `42`. Note that the name
of the variable used for the pointer is not important.

.. code-block:: cpp
  :linenos:
  :emphasize-lines: 3

  void foo() {
    int x = 42;
    // `x_ptr |-> intR 42 1`
    return x;
  }

|project| pointers and optional addresses
------------------------------------------

Pointers always contain an address, but |project| pointer values need not. In our
last example, `x` might live in a register or be removed altogether by
optimizations. But since |project| pointer values need not have an address, we can
reason about `x_ptr` uniformly, irrespective of optimizations.

We use the function |link:bluerock.lang.cpp.semantics.ptrs#PTRS.ptr_vaddr| to compute the
virtual address of a pointer.

.. code-block:: coq

  Parameter ptr_vaddr : ptr -> option vaddr.

Pointer provenance in |project|
================================================

Each (valid) pointer value must contain an allocation ID. This ID identifies the complete
object that the pointer refers to; similar concepts are common in modern
formalizations of pointers, from `CompCert <https://hal.inria.fr/hal-00703441/document>`_ onwards.

Notably, a single call to :cpp:`malloc` might allocate storage for multiple objects:
each such object will have a distinct allocation ID\ [#invalid-ptr-no-alloc-id]_.

.. code-block:: coq

  Parameter ptr_alloc_id : ptr -> option alloc_id.

Importantly, the ID of a complete object differs from the ID of any character
array that provides storage to the object.

.. _pointers-and-pointer-provenance.provenance.subobjects:

Pointers and subobjects in |project|
------------------------------------
A pointer identifies a "path" inside the complete object, where each
step goes to a subobject; this is less common, but follows both Krebbers (2015)
for C and Ramananandro for C++. For instance:

- if pointer `p` points to a `struct` instance, then pointer `p ., _field field`
  points to the field identified by `field`.
- if pointer `p` points to an array of 10 integers (hence, also to its first element),
  then pointer `p ., _sub Tint 1` points to the second element.

Above, `p ,. o` represents the pointer resulting from applying the *pointer offset* `o`
to the pointer `p`, and is a notation for `_offset_ptr p o`.
To simplify reasoning about pointers, we provide an equational theory of pointer
equality, which helps us show that C++ snippets such as `p + 2` and `p + 1 + 1`
produce the same pointer.

Pointer offsets form a *monoid* under concatenation, and |link:bluerock.lang.cpp.semantics.ptrs#PTRS._offset_ptr| represent
their *monoid action* over pointers. That is, we can compose offsets (via
|link:bluerock.lang.cpp.semantics.ptrs#PTRS.o_dot|, also written `.,`), this composition has an identity (|link:bluerock.lang.cpp.semantics.ptrs#PTRS.o_id|) and is
associative, and compositions with pointers is well-behaved. Moreover, specific
axioms allow us to collapse adjacent offsets, such as consecutive |link:bluerock.lang.cpp.semantics.ptrs#PTRS.o_sub| offsets.

Here are a few of the algebraic equations that apply to pointers and offsets.

.. code-block:: coq

    offset_ptr_id : p ., o_id = p
    offset_ptr_dot : p ., o1 ., o2 = p ., (o1 ., o2)

    id_dot : o ., o_id = o
    dot_id : o_id ., o = o
    dot_assoc : o1 ., (o2 ., o3) = (o1 ., o2) ., o3

    o_sub_0 : _sub ty 0 = o_id (* Under side conditions on [ty] *)
    o_dot_sub : _sub T n1 ., _sub T n2 = _sub T (n1 + n2)

This is formalized in Coq in |link:bluerock.lang.cpp.semantics.ptrs|.

Integer-pointer casts
---------------------

Beyond what is provided by the C++ standard, we assume useful semantics for
integer-to-pointer casts, in particular, the PNVI-ae-udi model by the Cerberus
project (as in the `N2577 paper from the C standard committee <http://www.open-std.org/jtc1/sc22/wg14/www/docs/n2577.pdf>`_).
As in Cerberus:

- Casting a pointer to an integer marks the allocation ID of the pointer as *exposed*.
- Casting an integer to a pointer can produce any pointer with the same address
  so long as that pointer's allocation ID has *already* been exposed.

However, some twists are required to account for the more complex memory model
from the C++ semantics. **Unlike in Cerberus**, more than two allocation IDs can cover
the same address. In C complete objects are generally disjoint, except that a past-the-end-pointer
can overlap with a pointer to another object. However, in C++ a complete object
with pointer `p` (with provenance `aid1 : alloc_id`) can be nested within a
character array that provides storage to it (with provenance `aid2`), which can
be nested inside another character array providing storage to it (with
provenance `aid3`), and so on. We assume that each of those provenances can be exposed
indipendently; casting the integer address of `p` to a pointer follows the same
rules as above, so it can produce a pointer with any exposed allocation IDs.

In all cases, we assume the C++ abstract machine follows an extension of the
PNVI-ae-udi model; in particular, the provenance remains ambiguous until such a point
that all provenances except for one can be shown to produce undefined behavior.

.. _no-pointer-zapping:

Assumptions beyond the standard
================================================

As our goal is verifying low-level systems software, we make
assumptions on our compilers, here and elsewhere:

- We assume compilers do not zap pointers to deallocated objects, but might
  restrict operations on them (in particular equality comparisons). See
  `Pointer lifetime-end zap (N2369) <http://www.open-std.org/jtc1/sc22/wg14/www/docs/n2369.pdf>`_,
  `C memory object and value semantics: the space of de facto and ISO standards
  <https://www.cl.cam.ac.uk/~pes20/cerberus/notes30.pdf>`_.
- Support for effective types is also incomplete; similarly to Cerberus,
  we still assume users use options such as GCC/Clang's `-fno-strict-aliasing`.

Further readings
================================================

For a crash course on formal models of pointers, consider also
`this blog post by Ralf Jung <https://www.ralfj.de/blog/2018/07/24/pointers-and-bytes.html>`_.

.. rubric:: Footnotes
.. [#objects-have-values] This appears to follow from `intro.object#1
  <https://eel.is/c++draft/intro.object#1>_,
  `basic.life#4 <https://eel.is/c++draft/basic.life#4>`_ and
  `basic.types.general#def:value <https://eel.is/c++draft/basic.types.general#def:value>`_.
  In particular, `basic.life#4 <https://eel.is/c++draft/basic.life#4>`_ licenses compilers to discard object contents
  outside their lifetime even in surprising scenarios; e.g. placement new over
  initialized memory is allowed to discard the initialization, even when the
  constructor is a no-op.
.. [#std-ptr-values] "Values of pointer type" are discussed in `basic.compound#3
  <https://eel.is/c++draft/basic.compound#3>`_.

.. [#invalid-ptr-no-alloc-id] The reason that this function is partial is because invalid pointers do not contain allocation IDs.
