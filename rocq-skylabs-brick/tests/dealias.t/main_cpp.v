Require Import bluerock.lang.cpp.parser.plugin.cpp2v.
cpp.prog source prog cpp:{{
  using Tr = int&;
  using Trr = int&&;
  using Tr_r = Tr&;
  using Tr_rr = Tr&&;
  using Trr_r = Trr&;
  using Trr_rr = Trr&&;
  using cTr = const int&;
  using cTrr = const int&&;
  using cTr_r = cTr&;
  using cTr_rr = cTr&&;
  using cTrr_r = cTrr&;
  using cTrr_rr = cTrr&&;
}}.

Require Import bluerock.lang.cpp.syntax.dealias.

Notation TEST input output :=
  (eq_refl : trace.runO (resolveValue source input%cpp_name) = Some output%cpp_name).

Succeed Example _1 := TEST "test(int)" "test(int)".
Succeed Example _1 := TEST "test(Tr)" "test(int&)".
Succeed Example _1 := TEST "test(Trr)" "test(int&&)".
Succeed Example _1 := TEST "test(Tr&)" "test(int&)".
Succeed Example _1 := TEST "test(Trr&)" "test(int&)".

Succeed Example _1 := TEST "test(Tr_r)" "test(int&)".
Succeed Example _1 := TEST "test(Tr_rr)" "test(int&)".
Succeed Example _1 := TEST "test(Trr_r)" "test(int&)".
