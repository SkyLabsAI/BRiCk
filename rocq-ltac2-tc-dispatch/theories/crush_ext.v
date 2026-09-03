Require Import skylabs.ltac2.extra.extra.
Require Import skylabs.ltac2.tc_dispatch.lookup.

Import Ltac2.

(**
[crush_ext] is An extensible version of [crush].

Users can add new tactics / strategies by adding [Ltac2Lookup] hints
[crush_ext] is An extensible version of [crush].

Users can add new tactics / strategies by adding [Dispatch] hints
to the [crush_ext] database.
 *)

Create HintDb crush_ext discriminated.

Module ltac2.
    Import Ltac2.Init.
    Import Ltac2.Notations.
    Ltac2 crush2 () :=
      let dbs := [Option.get (Std.find_hint_db ident:(crush_ext))] in
      repeat (goal_dispatch_with dbs).
End ltac2.

Ltac crush_ext :=
    ltac2:(ltac2.crush2 ()).
