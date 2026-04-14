(*
 * Copyright (C) 2021-2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** Extension of [Stdlib.Buffer]. *)

include module type of Stdlib.Buffer

(** [iter f b] calls [f] on each character of buffer [b] in order. In the case
    where [f] modifies [b] while iterating, the behaviour is unspecified. *)
val iter : (char -> unit) -> t -> unit

(** [iter_lines f b] calls [f] on every line of [b] (delimited by ['\n']). The
    trailing newline is not included when calling [f]. As for [iter], function
    [f] should not modify [b] while iterating. *)
val iter_lines : (string -> unit) -> t -> unit

(** [is_empty b] indicates whether the buffer [b] is empty. *)
val is_empty : t -> bool

(** [add_full_channel b ic] reads all characters on the input channel [ic] and
    adds them to [b]. This assumes that [ic] is not an endless stream. *)
val add_full_channel : t -> In_channel.t -> unit

(** [add_file b file] adds the contents of [file] to [b]. *)
val add_file : t -> Filepath.t -> unit

(** [from_file file] creates a new buffer whose initial contents is taken from
    the given [file]. *)
val from_file : Filepath.t -> t

(** [to_file file b] writes the contents of [b] to [file]. *)
val to_file : Filepath.t -> t -> unit
