Require Import bluerock.lang.cpp.syntax.supported.

Require test.test_cpp.

Eval vm_compute in supported.check.translation_unit test_cpp.module.
