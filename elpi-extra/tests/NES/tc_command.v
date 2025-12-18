(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

Require Import skylabs.elpi.extra.NES.

Elpi Command test.
#[phase="both"] Elpi Accumulate Db NES.db.
#[phase="both"] Elpi Accumulate File skylabs.elpi.extra.NES.code.
