Require Import bluerock.lang.cpp.parser.
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.

#[duplicates(warn)]
cpp.prog source1 prog cpp:{{
      struct C {
          int x{0};
      };
      void test() {
          auto x_p = &C::x;
          C c;
          (void)(c.*x_p);
      }
 }}.

Check source1.
