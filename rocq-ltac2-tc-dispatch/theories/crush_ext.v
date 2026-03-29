Require Ltac2.Ltac2.
Require Import skylabs.ltac2.tc_dispatch.lookup.

(**
[crush_ext] is An extensible version of [crush].

Users can add new tactics / strategies by adding [Ltac2Lookup] hints
to the [crush_ext] database.
 *)

Create HintDb crush_ext discriminated.

Module ltac2.
    Import Ltac2.Init.
    Import Ltac2.Notations.
    Ltac2 crush2 () :=
      let dbs := Some [ident:(crush_ext)] in
      repeat (ltac2.goal_dispatch_with dbs).
End ltac2.

Ltac crush_ext :=
    ltac2:(ltac2.crush2 ()).
