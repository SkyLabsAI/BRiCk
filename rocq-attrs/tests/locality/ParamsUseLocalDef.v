Require Import attrs.ParamsAttr.
From attrs_tests.locality Require Import ParamsLocalDef.

Fail Definition local_f_bad : Params ParamsLocalDef.local_f 0 :=
  ltac:(typeclasses eauto).
Fail Definition local_sec_bad : Params (@ParamsLocalDef.local_sec) 2 :=
  ltac:(typeclasses eauto).
