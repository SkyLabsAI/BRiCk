Require Import skylabs.ltac2.logger.logger.

Ltac2 Log Flag test.
Ltac2 Dev Log Flag test_dev.

Ltac2 Eval log[test] "test".
    
Ltac2 test1 () : message -> unit := printf "%m".
Ltac2 test2 () : message -> unit := log[test,10] "%m".
