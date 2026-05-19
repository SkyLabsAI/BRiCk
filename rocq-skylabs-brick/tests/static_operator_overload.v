Require Import skylabs.lang.cpp.syntax.typed.
Require Import skylabs.lang.cpp.cpp.

Require Import skylabs.lang.cpp.parser.plugin.cpp2v.

#[duplicates(error)]
cpp.prog source flags "-std=c++23" prog cpp:{{

struct C {
  static int operator()() { return 0; }
  static int& operator()(int& x) { return x; }
  static int&& operator()(int&& x) { return static_cast<int&&>(x); }
  operator bool() const { return true; }
};

void test() {
    C c;
    int x = 1;
    c();
    (void)c(x);
    (void)c(static_cast<int&&>(x));
    (void)(bool)c;
}

}}.

(* TODO: expand the test case to show that the *)
Goal trace.runO (decltype.check_tu source) = Some tt.
Proof. vm_compute. reflexivity. Qed.
