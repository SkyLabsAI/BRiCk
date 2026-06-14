Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.

cpp.prog module prog cpp:{{
  static_assert(true, "truth survives parsing");
  static_assert(true);
}}.

Goal module.(asserts) =
  [Build_StaticAssert "" (Ebool true);
   Build_StaticAssert "truth survives parsing" (Ebool true)]%pstring.
Proof. reflexivity. Qed.

cpp.prog ordered prog cpp:{{
  static_assert(true, "a");
  static_assert(true, "b");
}}.

cpp.prog permuted prog cpp:{{
  static_assert(true, "b");
  static_assert(true, "a");
}}.

Goal ordered = permuted.
Proof. reflexivity. Qed.
