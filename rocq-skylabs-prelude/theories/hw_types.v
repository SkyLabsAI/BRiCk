(*
 * Copyright (c) 2020-21 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.prelude.base.
Require Import bluerock.prelude.numbers.
Require Export bluerock.prelude.wrap.

Module int_line.
  Include wrapper.
End int_line.

Module time.
  Include wrapper.
End time.

Module cpu.
  Include wrapper.

  (* Valid CPU IDs range from [0] to [max - 1]. *)
  Definition count : N := pow2N 16.
  Definition max : t := of_N (count - 1).
End cpu.
Notation cpuT := cpu.t (only parsing).

Module mmio_idx.
  Include wrapper.
End mmio_idx.

Module size_bytes.
  Include wrapper.
End size_bytes.

(*
Module [types] is only used for compatibility with some clients.
TODO FM-643: flatten this module once clients are migrated. *)
Module Export types.
  Notation int_line := int_line.t (only parsing).
  Notation Build_int_line := int_line.of_N (only parsing).
  Notation get_int_line := int_line.to_N (only parsing).

  Notation time := time.t (only parsing).
  Notation Build_time := time.of_N (only parsing).
  Notation get_time := time.to_N (only parsing).

  Notation cpu := cpu.t (only parsing).
  Notation Build_cpu := cpu.of_N (only parsing).
  Notation get_cpu := cpu.to_N (only parsing).

  Notation mmio_idx := mmio_idx.t (only parsing).
  Notation Build_mmio_idx := mmio_idx.of_N (only parsing).
  Notation get_mmio_idx := mmio_idx.to_N (only parsing).

  Notation size_bytes := size_bytes.t (only parsing).
  Notation Build_size_bytes := size_bytes.of_N (only parsing).
  Notation get_size_bytes := size_bytes.to_N (only parsing).
End types.
