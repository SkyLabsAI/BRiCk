(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.

 * ALL of the following code is derived from code original to the
 * Iris project. That original code is
 *
 *	Copyright Iris developers and contributors
 *
 * and used according to the following license.
 *
 *	SPDX-License-Identifier: BSD-3-Clause
 *
 * Original Iris License:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/cb324b81f5b00a7cb8ae186d7aca5011350037cd/LICENSE-CODE
 *)

(**
This generalize [iris.program_logic.weakestpre.irisGS_gen]
(in `iris/program_logic/weakestpre.v`) to any PROP.

TODO : upstream.
*)
Require Export iris.base_logic.lib.fancy_updates.
Require Export iris.program_logic.language.
Require Export iris.bi.weakestpre.

Class irisGS_gen (Λ : language) (PROP : bi) `{FUpd PROP} := IrisG {

  (** The state interpretation is an invariant that should hold in
  between each step of reduction. Here [Λstate] is the global state,
  the first [nat] is the number of steps already performed by the
  program, [list (observation Λ)] are the remaining observations, and the
  last [nat] is the number of forked-off threads (not the total number
  of threads, which is one higher because there is always a main
  thread). *)
  state_interp : state Λ → nat → list (observation Λ) → nat → PROP;

  (** A fixed postcondition for any forked-off thread. For most languages, e.g.
  heap_lang, this will simply be [True]. However, it is useful if one wants to
  keep track of resources precisely, as in e.g. Iron. *)
  fork_post : val Λ → PROP;

  (** The number of additional logical steps (i.e., later modality in the
  definition of WP) and later credits per physical step is
  [S (num_laters_per_step ns)], where [ns] is the number of physical steps
  executed so far. We add one to [num_laters_per_step] to ensure that there
  is always at least one later and later credit for each physical step. *)
  num_laters_per_step : nat → nat;

  (** When performing pure steps, the state interpretation needs to be
  adapted for the change in the [ns] parameter.

  Note that we use an empty-mask fancy update here. We could also use
  a basic update or a bare magic wand, the expressiveness of the
  framework would be the same. If we removed the modality here, then
  the client would have to include the modality it needs as part of
  the definition of [state_interp]. Since adding the modality as part
  of the definition [state_interp_mono] does not significantly
  complicate the formalization in Iris, we prefer simplifying the
  client. *)
  state_interp_mono σ ns κs nt:
    state_interp σ ns κs nt ⊢ |={∅}=> state_interp σ (S ns) κs nt
}.
Global Arguments IrisG {Λ PROP _}.
