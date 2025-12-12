Require Import bluerock.lang.cpp.parser.plugin.cpp2v.
cpp.prog source prog cpp:{{
  namespace X {
    inline namespace Y {
      struct C { };
      using T = int;
      using Ca = C;
      int foo();
      int baz(int) { return 0; }

      template<typename T>
      int bar(T&) {
        return 0;
      }
    }
  }
  void test() {
    using namespace X::Y;
    int x;
    C c;
    bar<int&>(x);
    bar<int&&>(x);
    bar<const int&>(x);
    bar<const int&&>(x);

    bar<C&>(c);
    bar<C&&>(c);
    bar<const C&>(c);
    bar<const C&&>(c);
  }
}}.

Require Import bluerock.lang.cpp.syntax.dealias.

Notation TEST input output :=
  (trace.runO (resolveValue source input%cpp_name) = Some output%cpp_name) (only parsing).

Example s_1 : TEST "X::foo()" "X::Y::foo()".
Proof. compute. reflexivity. Qed.
Example s_2 : TEST "X::Y::foo()"  "X::Y::foo()".
Proof. compute. reflexivity. Qed.

Example baz_1 : TEST "X::baz(const int)" "X::Y::baz(int)".
Proof. compute. reflexivity. Qed.
Example baz_2 : TEST "X::Y::baz(const int)"  "X::Y::baz(int)".
Proof. compute. reflexivity. Qed.

Example bar_int_1 : TEST "X::bar<int&>(int&)" "X::Y::bar<int&>(int&)".
Proof. compute. reflexivity. Qed.
Example bar_int_2 : TEST "X::Y::bar<int&>(int&)" "X::Y::bar<int&>(int&)".
Proof. compute. reflexivity. Qed.
Example bar_int_3 : TEST "X::bar<int&&>(int&)" "X::Y::bar<int&&>(int&)".
Proof. compute. reflexivity. Qed.
Example bar_int_4 : TEST "X::bar<const int&>(const int&)" "X::Y::bar<const int&>(const int&)".
Proof. compute. reflexivity. Qed.
Example bar_int_5 : TEST "X::bar<const int&&>(const int&)" "X::Y::bar<const int&&>(const int&)".
Proof. compute. reflexivity. Qed.

Example bar_T_1 : TEST "X::bar<X::T&>(int&)" "X::Y::bar<int&>(int&)".
Proof. compute. reflexivity. Qed.
Example bar_T_2 : TEST "X::Y::bar<X::Y::T&>(X::T&)" "X::Y::bar<int&>(int&)".
Proof. compute. reflexivity. Qed.
Example bar_T_3 : TEST "X::bar<X::T&&>(X::Y::T&)" "X::Y::bar<int&&>(int&)".
Proof. compute. reflexivity. Qed.
Example bar_T_4 : TEST "X::bar<const X::Y::T&>(const X::T&)" "X::Y::bar<const int&>(const int&)".
Proof. compute. reflexivity. Qed.
Example bar_T_5 : TEST "X::bar<const X::T&&>(const X::Y::T&)" "X::Y::bar<const int&&>(const int&)".
Proof. compute. reflexivity. Qed.
