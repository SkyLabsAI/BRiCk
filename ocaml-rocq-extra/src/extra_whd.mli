(*
 * Copyright (C) 2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** [eval ?share env sigma flags t] performs weak head reduction on [t]
    according to [flags]. It can be partially applied up to [flags] and the
    result can be re-used to reduce constrs provided they come from the original
    [env] and [sigma]. *)
val eval :
  ?share:bool ->
  Environ.env ->
  Evd.evar_map ->
  RedFlags.reds ->
  EConstr.t ->
  EConstr.t
