(*
 * Copyright (C) 2021-2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(** Stream / co-list *)

(** Type of a stream (or co-list) holding values of type ['a]. *)
type 'a t

(** [of_seq it] turns the given iterator [it] into a steam. *)
val of_seq : 'a Seq.t -> 'a t

(** [next s] returns the next element in the stream [s], if any. *)
val next : 'a t -> 'a option

(** [from f] builds a stream from the function [f]. *)
val from : (unit -> 'a option) -> 'a t
