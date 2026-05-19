(** Command options for [dune-rocqdeps]. *)
type options = {no_normalize: bool}

val run : options -> unit
(** Run the dependency synchronization tool for the current workspace and
    current working directory subtree. *)
