Require Import skylabs.lang.cpp.syntax.mtyped.
Require Import test_20_cpp test_20_cpp_templates.

Succeed Example _0 : check_mtu templates source = trace.Success tt := eq_refl.
