type t
(** Opaque dune workspace handle. *)

val current : unit -> t
(** Discover the current dune workspace from the process environment or by
    walking upward from the current directory. *)

val root : t -> Fpath.t
(** Absolute normalized workspace root directory. *)

val dune_files : t -> Fpath.t list
(** All [dune] files reachable from the workspace root, excluding pruned
    directories such as [.git], [_build], and [_opam]. *)
