#################
Acknowledgements
#################

BRiCk builds on a significant amount of past work and tools.

Projects
=========
* The RustBelt Project
* Ralf Jung (`<https://people.mpi-sws.org/~jung/>`__; `<https://www.ralfj.de/blog/>`__
  Work on RustBelt + experience with clang => a sounding board when we have questions
* `Robbert Krebbers' PhD Disseration <https://robbertkrebbers.nl/thesis.html>`_
  Formalized a sequential subset of C - CH2O - in coq => where C and C++ overlap we can use his ideas directly; if C and C++ diverge, we can modify/build-on his work.

C++ (and C) Semantics
=======================
* `The C++ Standard <https://eel.is/c++draft/>`__
* `CompCert <https://compcert.org/compcert-C.html>`__
  Verified compiler for a large subset of real-world C => insight into how we might architect our stack as we consider the (practical) boundaries of our TCB
* `The Verified Software Toolchain (VST) <https://vst.cs.princeton.edu/>`__
  Building on CompCert in order to provide a framework for specifying and verifying C programs written in the appropriate subset of the language
* `The Cambridge University REMS Group <https://www.cl.cam.ac.uk/~pes20/rems/>`__, especially the `Cerberus project <https://www.cl.cam.ac.uk/~pes20/cerberus/>`__
* `Robbert Krebbers' PhD Disseration <https://robbertkrebbers.nl/thesis.html>`_
* `John Regehr <https://www.cs.utah.edu/~regehr/>`_
* `Pascal Cuoq <https://stackoverflow.com/users/139746/pascal-cuoq>`_


Separation Logic (Iris)
========================
* `The Iris Project <https://iris-project.org/>`_ provides the separation logic that we build our program logic on top of.

..
  The main infrastructure which underlies all of the formalizations which we rely on to actually verify programs written using our C++-AST/Axiomatic Semantics
