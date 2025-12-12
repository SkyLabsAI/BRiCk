.. _evaluation:

###############################
Evaluation
###############################

The semantics of C++ programs in |project| are written in `weakest (liberal) pre-condition style <https://en.wikipedia.org/wiki/Predicate_transformer_semantics>`_.
The general form of these rules is the following:

.. coq:

   Parameter wp : input_1 -> .. -> input_n -> (output_1 -> ... -> output_n -> PROP) -> PROP

Note that `wp` is a predicate in our separation logic (the fact that it returns a `PROP`).
Informally you can think of it as capturing the pre-condition to the inputs (one of which is normally an expression) that are sufficient such that the code is safe and if the expression terminates, it terminates in a state in which its outputs satisfy the "continuation" (i.e. the final function argument to `wp`).

Due to the structure of C++, |project| contains a separate weakest pre-condition modality for each syntactic category. These are defined in |link:bluerock.lang.cpp.logic.wp|.

Expressions
==============

In |project| we break expression evaluation down into four weakest pre-condition assertions representing the different `value categories <http://eel.is/c++draft/expr.prop#basic.lval-1>`_ of a C++ expression.

Modeling Temporaries
---------------------

In the course of evaluating C++ programs, the language can construct objects that are later destroyed, this occurs for `automatic storage duration <https://eel.is/c++draft/basic.stc.auto#1>`_ variables (i.e. stack allocated variables and temporaries).
C++ semantics guarantees that the lifetime of temporaries is well-bracketed, meaning that objects will be destroyed in the reverse order that they were constructed.
In |project| we capture the stack of objects to be destroyed using the type |link:bluerock.lang.cpp.logic.wp#FreeTemps.t|.

.. literalinclude:: ../../theories/lang/cpp/logic/wp.v
   :start-after: (* BEGIN FreeTemps.t *)
   :end-before: (* END FreeTemps.t *)
   :dedent:

Here |link:bluerock.lang.cpp.logic.wp#FreeTemps.id| represents the identity, characterizing that nothing needs to be destroyed.
`delete ty p` represents that the value at pointer `p` (which should have type `ty`) needs to be destroyed.
Note that to delete the value, the C++ abstract machine runs the destructor and reclaims the underlying memory.
Virtual dispatch is *not* used when invoking the destructor.
`seq a b` means that the temporaries in `a` must be destroyed *before* the temporaries in `b`.
`par a b` means that the temporaries in `a` and the temporaries in `b` are destroyed in an interleaved manner [#parallel-destruction]_.

The meaning of these constructs is made precise by interpreting the syntax using |link:bluerock.lang.cpp.logic.destroy#interp|.

.. literalinclude:: ../../theories/lang/cpp/logic/destroy.v
   :start-after: (* BEGIN interp *)
   :end-before: (* END interp *)
   :dedent:

l-values & x-values
----------------------

l-values and x-values follow the same general structure.
Their weakest precondition rules are captured by |link:bluerock.lang.cpp.logic.wp#WPE.wp_lval| and |link:bluerock.lang.cpp.logic.wp#WPE.wp_xval| respectively (we show `wp_lval` as our example).

.. literalinclude:: ../../theories/lang/cpp/logic/wp.v
   :start-after: (* BEGIN wp_lval *)
   :end-before: (* END wp_lval *)
   :dedent:

pr-values
----------------------

The final value category of C++ (pr-values) is slightly more complex than l-values and x-values.
The `C++ standard <http://eel.is/c++draft/expr.prop#basic.lval-1.2>`_ describes them as follows:

.. quote:

   A prvalue is an expression whose evaluation initializes an object or
   computes the value of an operand of an operator, as specified by the
   context in which it appears, or an expression that has type cv void."

These are characterized by two predicate transformers.

Operands
~~~~~~~~~~~
|link:bluerock.lang.cpp.logic.wp#WPE.wp_operand| is used to evaluate a operand of a primitive operator.
These operands are *always* primitives, since operators that accept aggregates are de-sugared to functions or methods.

.. literalinclude:: ../../theories/lang/cpp/logic/wp.v
   :start-after: (* BEGIN wp_operand *)
   :end-before: (* END wp_operand *)
   :dedent:

Unlike `wp_init` and `wp_prval`, operands return |link:bluerock.lang.cpp.semantics.value#val|\ s.
Because the value returned does not have an identity, there is nothing to destroy, so the `FreeTemps` returned to the continuation destroys only the temporaries created when evaluating the expression.


Initializing Aggregates
~~~~~~~~~~~~~~~~~~~~~~~~

|link:bluerock.lang.cpp.logic.wp#WPE.wp_init| handles initialization of aggregates.
The parameter is the following:

.. literalinclude:: ../../theories/lang/cpp/logic/wp.v
   :start-after: (* BEGIN wp_init *)
   :end-before: (* END wp_init *)
   :dedent:

`wp_init` takes a |link:bluerock.lang.cpp.semantics.values#PTRS.ptr| that represents the location that the object is being constructed into.
Because of this, the post-condition does not consume a value but only a `FreeTemps` used to destroy temporaries created during the evaluation of the expression.
To destroy the actual object constructed by `wp_init ty into Q`, use `FreeTemps.delete ty into`.

On top of `wp_init`, we can *define* `wp_prval` by universally quantifying the pointer that is being initialized and passing it to the continuation.

.. literalinclude:: ../../theories/lang/cpp/logic/wp.v
   :start-after: (* BEGIN wp_prval *)
   :end-before: (* END wp_prval *)
   :dedent:

Note that the pointer `p` is completely unconstrained in this definition.
In practice the C++ abstract machine will pick this pointer to be fresh and reserve it before proceeding to initialize during the evaluation of `e`.

Initialization
----------------

Initialization is slightly more complex than `wp_init` because you can initialize aggregates (using `wp_init`), primitives (using `wp_operand`), and references (using `wp_lval` and `wp_xval`).
To capture this, |project| *defines* `wp_initialize` which provides the semantics to materialize a value into the C++ abstract machine state (which |project| reflects through separation logic assertions such as `primR`).
`wp_initialize` is defined by induction on the type of the value being initialized with special handling of `const` qualifiers.

.. literalinclude:: ../../theories/lang/cpp/logic/initializers.v
   :start-after: (* BEGIN wp_initialize *)
   :end-before: (* END wp_initialize *)
   :dedent:


Function Call Semantics
------------------------

The semantics for function calls is concerned with the way that we pass arguments to functions and (potentially) receive the return value.
We note that it is important to handle the passing of primitives as well as aggregates, both of which are very common in C++.
The semantics for function calls specifies how to pass arguments to functions and (potentially) get back the return value, both for primitives and for aggregates.

|project| follows the C++ standard by `using initialization semantics to pass (and return) data to (and from) functions <https://eel.is/c++draft/expr.call#7>`_.
It is also the style taken by `Cerberus <https://www.cl.cam.ac.uk/~pes20/cerberus/>`_.

C++ leaves the lifetime of *trivially destructible* function arguments unspecified, as it is *generally* not visible to client programs.
|project| follows the Itanium ABI as is documented in |link:bluerock.lang.cpp.logic.call|.

.. literalinclude:: ../../theories/lang/cpp/logic/call.v
   :start-after: BEGIN destruction-of-function-arguments
   :end-before: END destruction-of-function-arguments
   :dedent:


.. rubric:: Footnotes
.. [#parallel-destruction] `par` can be used to describe the semantics of destruction in C, it is not needed for the semantics of C++ because C++ defines evaluation order as non-deterministic interleaving.
