Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.syntax.supported.

Require test.test_cpp.

(* A record with bit-fields is an opaque record: its size and alignment are
   kept, and the translation unit is supported. *)
Eval vm_compute in types test_cpp.source !! "C"%cpp_name.
Eval vm_compute in supported.check.translation_unit test_cpp.source.
