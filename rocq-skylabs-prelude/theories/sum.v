(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.prelude.base.

Module sum.
  Definition existsb {A B} (f : A -> bool) (g : B -> bool) (s : A + B) : bool :=
    match s with
    | inl a => f a
    | inr b => g b
    end.
End sum.
