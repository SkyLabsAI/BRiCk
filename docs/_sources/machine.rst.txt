.. _machine-interop:

#############################################################
Assembly Interoperation
#############################################################

This section describes the mechanisms that |project| uses to connect C++ concepts to the underlying generated machine code.
These connections are generally necessary in low-level code that inter-operates with assembly.
For example, accessing C++ memory from assembly, calling C++ functions from assembly, changing the address space that the C++ program is running in, etc.

While crucial for low-level programs these features are generally not used in high-level programs.
Even for low-level programs, a relatively small amount of the program requires properties at this level.

Compiler Correctness
=====================

|project|'s strategy for connecting C++ programs to machine programs is to connect the weakest pre-condition of C++ functions to a weakest pre-condition for machine code.
The relevant definitions can be found in |link:skylabs.lang.cpp.compile|.

.. literalinclude:: ../../theories/lang/cpp/compile.v
   :start-after: (* BEGIN COMPILE SNIPPET *)
   :end-before: (* END COMPILE SNIPPET *)

This approach effectively casts C++ as a stylized way to write machine code; however, it is more than simply macros.
When C++ code is running, the C++ abstract machines *owns* the underlying memory and can use that ownership to assert invariants over the memory (e.g. that code is not written, :cpp:`const` objects do not change, etc).
This characterization makes it possible (and even natural) to escape the abstract machine in limited circumstances and interact at a lower-level of abstraction.
For example, a viable model of inline assembly is to borrow resources from the abstract machine, run the assembly, and then return the underlying resources back to the abstract machine.
The :ref:`Object representation, layout and padding <object_layout>` section goes into more details regarding how this access to memory is coordinated within |project|.
