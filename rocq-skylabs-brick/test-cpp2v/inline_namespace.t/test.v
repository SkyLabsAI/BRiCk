Require Import bluerock.prelude.base.
Require Import bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.syntax.dealias.
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.

cpp.prog source prog cpp:{{
    namespace X {
      inline
      namespace Y {
        inline namespace Z {
          void testXYZ();
        }
        void testXY();
      }
      void testX();
    }
    inline namespace A {
      void testA();
    }
}}.

Notation TEST a b :=
  (dealias.resolveValue source a%cpp_name = trace.Success b%cpp_name) (only parsing).

Example _1 : TEST "X::testXYZ()" "X::Y::Z::testXYZ()" := eq_refl.
Example _12 : TEST "X::Y::testXYZ()" "X::Y::Z::testXYZ()" := eq_refl.
Example _2 : TEST "X::testXY()" "X::Y::testXY()" := eq_refl.
Example _3 : TEST "X::testX()" "X::testX()" := eq_refl.
Example _4 : TEST "testA()" "A::testA()" := eq_refl.
Example _5 : TEST "A::testA()" "A::testA()" := eq_refl.
