Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.

#[duplicates(error)]
cpp.prog source prog cpp:{{
  struct C1 { };
  struct C2 { C2() = default; };
  struct C3 { C3() = delete; };
  struct C4 { ~C4() = delete; };
}}.

Definition get (n : name) :=
  (n , source.(symbols) !! n).

Eval vm_compute in get "C1::C1()".
Eval vm_compute in get "C1::~C1()".
Eval vm_compute in get "C1::C1(const C1&)".
Eval vm_compute in get "C1::C1(const C1&&)".
Eval vm_compute in get "C1::operator=(const C1&)".
Eval vm_compute in get "C1::operator=(C1&&)".


Eval vm_compute in get "C2::C2()".
Eval vm_compute in get "C2::~C2()".
Eval vm_compute in get "C2::C2(const C2&)".
Eval vm_compute in get "C2::C2(const C2&&)".
Eval vm_compute in get "C2::operator=(const C2&)".
Eval vm_compute in get "C2::operator=(C2&&)".

Eval vm_compute in get "C3::C3()".
Eval vm_compute in get "C3::~C3()".
Eval vm_compute in get "C3::C3(const C3&)".
Eval vm_compute in get "C3::C3(const C3&&)".
Eval vm_compute in get "C3::operator=(const C3&)".
Eval vm_compute in get "C3::operator=(C3&&)".

Eval vm_compute in get "C4::C4()".
Eval vm_compute in get "C4::~C4()".
Eval vm_compute in get "C4::C4(const C4&)".
Eval vm_compute in get "C4::C4(const C4&&)".
Eval vm_compute in get "C4::operator=(const C4&)".
Eval vm_compute in get "C4::operator=(C4&&)".
