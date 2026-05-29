Require Import skylabs.lang.cpp.syntax.mtyped.
Require Import test_17_cpp test_17_cpp_templates.

Succeed Example _0 : check_mtu templates module = trace.Success tt := ltac:(vm_compute; reflexivity).
