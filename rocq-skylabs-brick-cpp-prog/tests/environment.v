(* The test deliberately omits -test-mode so failures containing physical
   environment configuration paths do not make the output checkout-dependent. *)
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.

From skylabs_cpp_prog.tests Extra Dependency "native_environment" as native_environment.
From skylabs_cpp_prog.tests Extra Dependency "invalid_environment" as invalid_environment.

(* The default invocation is unchanged. *)
cpp.prog native_source prog cpp:{{ void native_test() {} }}.
Goal native_source = native_source. Proof. reflexivity. Qed.

(* Configured native mode uses the shared adapter, with the normal frontend
   attributes and flags. No Docker daemon or installed-tool symlink is needed. *)
#[environment="native_environment", elaborate, check_types]
cpp.prog configured_source flags "-std=c++20" prog cpp:{{
  struct S { int value; };
  int configured_test() { return S{42}.value; }
}}.
Goal configured_source = configured_source. Proof. reflexivity. Qed.

(* Unknown dependency names and invalid runner configurations must not silently
   switch back to the native translator. *)
Fail #[environment="not_declared"]
cpp.prog missing_source prog cpp:{{ void test() {} }}.

Fail #[environment="invalid_environment"]
cpp.prog invalid_source prog cpp:{{ void test() {} }}.

(* The attribute is meaningful only on quotations, not pretranslated ASTs. *)
cpp.prog static_control defns skylabs.lang.cpp.parser.translation_unit._skip.
Goal static_control = static_control. Proof. reflexivity. Qed.
Fail #[environment="native_environment"]
cpp.prog static_source defns skylabs.lang.cpp.parser.translation_unit._skip.
