Require Import bluerock.lang.cpp.parser.
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.

#[duplicates(warn)]
cpp.prog source1 prog cpp:{{
      void test() { }
 }}.

Check source1.

#[duplicates(error)]
cpp.prog source2 prog cpp:{{
      int add(int x, int y) { return x + y; }
  }}.

Check source2.

Fail #[duplicates(ignore)]
cpp.prog buggy_source prog cpp:{{
  void identity(int x) { return x; }
}}.


Section code.
cpp.prog source3 prog cpp:{{
  void test(const int src1[], const int src2[], int dst[], int n) {
    // Sum the arrays src1 and src2 in dst
    for (int i = 0; i < n; i++) {
      dst[i] = src1[i] + src2[i];
    }
  }
}}.
End code.
