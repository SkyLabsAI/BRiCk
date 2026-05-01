type options = {no_normalize: bool}
(** Command options for [dune-rocqdeps]. *)

val run : options -> unit
(** Run the dependency synchronization tool for the current workspace and
    current working directory subtree. *)
