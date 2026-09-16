(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** Notation to attach a label at the start of the tactic implemention of a
    [Hint Extern], so that a name can be extracted for the hint. Here, a name
    is simply a reference to some definition, possibly a dummy definition that
    is specific for a given [Hint Extern]. *)
#[global] Tactic Notation "hint_label" reference(_r) := idtac.
