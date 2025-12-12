################################
The |project| C++ Program Logic
################################

|project| is a program logic for low-level, concurrent C++ built on the Iris separation logic.
|project|'s goal is to develop a clear and compositional semantics of C++ programs, that can be used across many levels of abstraction.

.. topic:: Note

   This repository does not provide usable verification tooling to apply these principles to real C++ programs.
   If you are interested in verifying real, concurrent C++ programs using this logic, please check out the `automation documentation <https://skylabs-ai.github.io/auto-docs>`_.
   `SkyLabs AI <https://skylabs-ai.com/>`_ has developed verification tools on top of this semantics that can be used to verify real C++ programs.

The |project| release contains two pieces:

* The cpp2v tool transforms C++ programs into a format that is digestible by the Coq proof assistant;
* The |project| program logic describes the meaning of C++ constructs in terms of reasoning principles that enable users to modularly derive the meaning of programs from their constituent pieces.

|project| focuses on a tailored (but relatively large) portion of modern C++.
Some high-level features (and non-features) include the following:

* |project| does not *currently* support some C++ features: e.g. member pointers, exceptions, goto, and virtual inheritance.
* |project| is currently limited to reasoning about templated code after it has been instantiated.
* Some features have restricted use: e.g. |project|'s support for switch statements does not support Duff's device.
* |project| adopts (limited) extensions to the C++ standard, based on existing research, e.g. for multi-address spaces, assembly interoperability, integer-to-pointer casts, and pointer provenance.

Our full feature set (as well as known issues) can be found on the :ref:`features <features>` page.

|project| is a work in progress. We welcome feedback, collaborations, and contributions.

.. toctree::
   :maxdepth: 2
   :caption: Table of Contents

   features
   evaluation
   undefined_behavior
   pointers
   object_layout
   machine
   documentation
   bibliography
   acknowledgements

.. todo:: actually do something with these
..
   Indices and tables
   ==================

   * :ref:`genindex`
   * :ref:`modindex`
   * :ref:`search`
