Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.syntax.typed.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.

cpp.prog source prog cpp:{{{
struct C {
  int data;
  C(int x):data(x) {}
};

struct D : C {
  int dd;
  using C::C;
};


void test() {
  D d(0);
}
}}}.

Eval vm_compute in decltype.check_tu source.
