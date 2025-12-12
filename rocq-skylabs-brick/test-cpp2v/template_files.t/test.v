Require Import bluerock.lang.cpp.syntax.supported.

Require test.test_cpp.
Require test.test_templates.

Eval vm_compute in supported.check.translation_unit test_cpp.source.
Eval vm_compute in supported.check.template_unit test_templates.templates.
