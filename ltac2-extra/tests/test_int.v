(*
 * Copyright (C) 2022-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Stdlib.Numbers.BinNums.
Require Stdlib.PArith.BinPos.
Require Import skylabs.ltac2.extra.internal.init.
Require Import skylabs.ltac2.extra.internal.int.

Module Type _Tests.
  Import Ltac2.

  Module Map.
    Goal True.
      let m := Int.Map.empty in
      let m := Int.Map.add 1 [] m in
      let m := Int.Map.add 2 ["test"] m in
      match Int.Map.find_opt 1 m with
      | Some [] =>
        let m := Int.Map.remove 1 m in
        let m := Int.Map.remove 2 m in
        if Int.Map.is_empty m then exact I else
          Control.throw (Invalid_argument None)
      | _ => Control.throw (Invalid_argument None)
      end.
    Qed.
  End Map.

End _Tests.
