(** Opaque dune workspace handle. *)
type t

val current : unit -> t
(** Discover the current dune workspace. *)

val root : t -> Fpath.t
(** Absolute normalized workspace root directory. *)

val dune_files : t -> Fpath.t list
(** All [dune] files reachable from the workspace root, excluding pruned
    directories such as [.git], [_build], and [_opam]. *)
