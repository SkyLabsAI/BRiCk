Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.lang.cpp.semantics.sub_module.

#[duplicates(error)]
cpp.prog header prog cpp:{{
  struct C {
  };
}}.

#[duplicates(error)]
cpp.prog cpp prog cpp:{{
  struct C {
  };

  void test() {
    C c;
  }
}}.

Example first_tu_sub_module_second_tu :
  bool_decide (sub_module header cpp) = true.
Proof. vm_compute. reflexivity. Qed.
