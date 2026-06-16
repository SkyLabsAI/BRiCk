Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.supported.
Require test.test_cpp.

Example generated_float_casts_supported :
  supported.check.translation_unit test_cpp.module = [] :=
  ltac:(vm_compute; reflexivity).
