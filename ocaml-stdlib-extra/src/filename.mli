(*
 * Copyright (C) 2025-2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

include module type of Stdlib.Filename

(** [decompose path] decomposes [path] into a triple [(dir, base, ext)], where
    [dir] is the directory part, [base] is the basename without extension, and
    [ext] is the extension including the leading dot, or the empty string when
    there is no extension. *)
val decompose : string -> string * string * string

(** [is_clean_relative path] indicates whether [path] is a relative path, that
    moreover does not mention the current or parent directory in its path. *)
val is_clean_relative : string -> bool
