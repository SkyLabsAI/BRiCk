Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require skylabs.lang.cpp.syntax.supported.


Require test.test_cpp.

Eval vm_compute in supported.check.translation_unit test_cpp.module.
