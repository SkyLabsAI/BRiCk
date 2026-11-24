Require Import skylabs.lang.cpp.syntax.supported.

Require test.asm_cpp test.coro_cpp.

Eval vm_compute in supported.check.translation_unit asm_cpp.source.
Eval vm_compute in supported.check.translation_unit coro_cpp.source.
