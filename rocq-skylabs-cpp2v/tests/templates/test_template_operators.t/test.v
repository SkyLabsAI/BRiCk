Require Import skylabs.lang.cpp.syntax.mtyped.
Require Import test_17_cpp test_17_cpp_templates.

Succeed Example _0 : check_mtu templates source = trace.Success tt := eq_refl.
