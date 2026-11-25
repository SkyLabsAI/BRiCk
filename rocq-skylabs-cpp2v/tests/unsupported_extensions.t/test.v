Require Import skylabs.lang.cpp.syntax.supported.

Require test.asm_cpp test.assume_cpp test.coro_cpp test.localdecl_cpp test.omp_cpp test.ms_cpp.

Eval vm_compute in supported.check.translation_unit asm_cpp.source.
Eval vm_compute in supported.check.translation_unit assume_cpp.source.
Eval vm_compute in supported.check.translation_unit coro_cpp.source.
Eval vm_compute in supported.check.translation_unit localdecl_cpp.source.
Eval vm_compute in supported.check.translation_unit omp_cpp.source.
Eval vm_compute in supported.check.translation_unit ms_cpp.source.
