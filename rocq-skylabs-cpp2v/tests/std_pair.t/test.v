Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require skylabs.lang.cpp.syntax.supported.


Require test.test_cpp.

Definition check_without_stdlib_long_double : supported.check.M :=
  List.filter
    (fun msg =>
       match PrimString.compare msg "Builtin long double"%pstring with
       | Eq => false
       | _ => true
       end)
    (supported.check.translation_unit test_cpp.source).

Eval vm_compute in check_without_stdlib_long_double.
