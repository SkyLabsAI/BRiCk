(** Input / output configuration. *)
type io =
  | Shell          (** Using the current program's shell. *)
  | Null           (** Redirecting to ["/dev/null"].      *)
  | File of string (** Redirecting to the specified file. *)

(** [exec ~cmd ?stdin ?stdout ?stderr args] replaces the current program using
    the command [cmd], with arguments [args],  redirecting inputs according to
    [stdin],  and redirecting outputs according to [stdout] and [stderr] (they
    default to [Shell] if they are omitted). In case of success, this function
    never returns, as control is fully transferred to the command. *)
val exec : cmd:string -> ?stdin:io -> ?stdout:io -> ?stderr:io ->
  string list -> 'a

(** [run ~cmd ?stdin ?stdout ?stderr args] executes the command [cmd] with the
    arguments [args], redirecting inputs according to [stdin], and redirecting
    outputs according to [stdout] and [stderr] (they default to [Null] if they
    are omitted). The return value is [Ok] if the command terminates normally,
    and it is [Error] if it terminates with a non-0 status. The payload of the
    [Error] constructor is the return code (if the program was not signaled or
    stopped) and a message explaining the error status. *)
val run : cmd:string -> ?stdin:io -> ?stdout:io -> ?stderr:io ->
  string list -> (unit, int option * string) result
