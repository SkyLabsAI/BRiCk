open Prelude

type t = string

val normalize : string -> string

val equal : t eq

(** Decomposed relative path to a file or directory. *)
type decomposed_rel_path = {
  path : string list;
  (** Directories on the path to the file. *)
  name : string;
  (** Base name of the file (without extension). *)
  ext  : string option;
  (** File extension if any. *)
}

val decompose : t -> decomposed_rel_path
