Require Import bluerock.lang.cpp.parser.
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.

Import Stdlib.Strings.String.
#[local] Open Scope string_scope.

Definition t_pre := "foo".


#[duplicates(warn)]
cpp.prog source1 prog cpp:{{
      void test() { }
 }}.

Definition t_post := "foo".

Goal (ltac:(let x := type of t_pre in exact x) = ltac:(let x := type of t_post in exact x)).
Proof. reflexivity. Qed.
