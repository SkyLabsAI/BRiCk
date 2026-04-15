type io =
  | Shell
  | Null
  | File of string

let from_io : io -> string option = fun io ->
  match io with
  | Shell   -> None
  | Null    -> Some("/dev/null")
  | File(f) -> Some(f)

let exec : cmd:string -> ?stdin:io -> ?stdout:io -> ?stderr:io ->
    string list -> 'a =
    fun ~cmd ?(stdin=Shell) ?(stdout=Shell) ?(stderr=Shell) args ->
  let stdin = from_io stdin in
  let stdout = from_io stdout in
  let stderr = from_io stderr in
  let cmd = Filename.quote_command cmd ?stdin ?stdout ?stderr args in
  Unix.execv "/bin/sh" [|"/bin/sh"; "-c"; cmd|]

let run : cmd:string -> ?stdin:io -> ?stdout:io -> ?stderr:io ->
    string list -> (unit, int option * string) result =
    fun ~cmd ?(stdin=Null) ?(stdout=Null) ?(stderr=Null) args ->
  match Unix.fork () with
  | 0   -> exec ~cmd ~stdin ~stdout ~stderr args
  | pid ->
  let (_, status) = Unix.waitpid [] pid in
  match status with
  | Unix.WEXITED(0)   -> Ok()
  | Unix.WEXITED(i)   ->
      Error(Some(i), Printf.sprintf "exited with code %i" i)
  | Unix.WSIGNALED(_) ->
      Error(None, "was killed by a signal")
  | Unix.WSTOPPED(_)  ->
      Error(None, "was stopped by a signal")
