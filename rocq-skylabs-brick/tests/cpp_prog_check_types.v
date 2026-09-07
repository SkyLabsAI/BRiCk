Require Import skylabs.lang.cpp.parser.plugin.cpp2v.

#[check_types]
cpp.prog checked_source prog cpp:{{
  struct Checked {
    int field;
  };

  int checked_global;
}}.

Goal checked_source = checked_source.
Proof. reflexivity. Qed.
