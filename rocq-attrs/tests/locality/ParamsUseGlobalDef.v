Require Import attrs.ParamsAttr.
From attrs_tests.locality Require Import ParamsGlobalDef.

Definition global_f_ok : Params global_f 0 := ltac:(typeclasses eauto).
Definition global_sec_ok : Params (@global_sec) 2 := ltac:(typeclasses eauto).
Fail Definition global_sec_old_bad : Params (@global_sec) 1 := ltac:(typeclasses eauto).
