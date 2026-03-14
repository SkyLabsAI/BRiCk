(*
 * Copyright (C) 2026 Skylabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.init.

Module Message.
  Import Ltac2.
  Export Message.

  Ltac2 join (sep : message) (msgs : message list) : message :=
    match msgs with
    | [] => Message.of_string ""
    | x :: xs =>
        let concat := List.fold_left Message.concat (Message.of_string "") in
        List.fold_left
          (fun x y => concat [x;sep;y])
          x xs
    end.

  Ltac2 join_lines (msgs : message list) : message :=
    join Message.force_new_line msgs.

  (* Shadow [Message.concat] to fit the same naming convention as [List] *)
  Ltac2 append := Message.concat.
  Ltac2 concat (l : message list) := List.fold_right Message.concat l Message.empty.

End Message.
