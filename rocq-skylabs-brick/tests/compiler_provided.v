Require Import skylabs.lang.cpp.cpp.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.

#[duplicates(warn)]
cpp.prog source prog cpp:{{
   struct C {};

   void test() {
       C c;
       c = c;
       c = static_cast<C&&>(c);
   }
}}.

Eval vm_compute in source.(symbols) !! "C::C()"%cpp_name.
Eval vm_compute in source.(symbols) !! "C::~C()"%cpp_name.
Eval vm_compute in source.(symbols) !! "C::operator=(const C&)"%cpp_name.
Eval vm_compute in source.(symbols) !! "C::operator=(C&&)"%cpp_name.
