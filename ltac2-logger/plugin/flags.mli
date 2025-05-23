type notations
val declare_ltac2_log_flag : Names.Id.t -> bool -> notations
val declare_ltac2_log_flag_interpretation : notations -> unit
val print_ltac2_log_flags : unit -> unit

type level = int

type flag

val repr : flag Ltac2_plugin.Tac2ffi.repr

val get_level : flag -> level
val max_level : unit -> level

val enabled : flag -> level -> bool

val log_level : level -> Logger_lib.Logger.Metadata.t
val log_flag  : flag  -> Logger_lib.Logger.Metadata.t
