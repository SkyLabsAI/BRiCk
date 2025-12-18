open Stdlib_extra.Extra
open Logger_lib.Logger

let no_events_level_0 =
  CWarnings.create
    ~name:"sl-log-empty"
    ~default:CWarnings.Enabled
    (fun msg -> msg)

(** [output_log debug opath] outputs the currently recorded log. If [debug] is
    [false], then an error is triggered in the case where the log is not well-
    formed (i.e., all open spans are closed). If [opath] is [None] the the log
    is shown in the Coq buffer. If [opath] is a file to a txt or JSON file, it
    is used as target, and the contents is written with the appropriate format
    (determined according to the extension). If an error occurs, the [Failure]
    exception is raised with an informative message. *)
let output_log : bool -> string option -> unit = fun debug opath ->
  (* We give a warning if the levels are all 0 and the logs are empty. *)
  if Flags.max_level () = 0 && Log.count_events () = 0 then
    begin
      let hint = "Did you forget to use [Set SL Debug \"@default=1\".]?" in
      let msg = "all levels are 0, and there are no events.\n" ^ hint in
      no_events_level_0 (Pp.str msg)
    end;
  match opath with
  | Some(path) -> Log.write ~debug path
  | None       ->
  let b = Log.write_buffer ~debug () in
  Buffer.iter_lines (fun l -> Feedback.msg_notice (Pp.str l)) b

(** [output_log_tmp debug ext] is the same as [output_log debug (Some(file))],
    where [file] is a fresh temporary file with extension [ext] (starting with
    a dot). After the log has been output, the name of the temporary file that
    was chosen is displayed in the Coq buffer (at level "notice"). If an error
    occurs, the [Failure] exception is raised with an informative message. *)
let output_log_tmp : bool -> string -> unit = fun debug ext ->
  let path = Log.write_tmp ~debug ext in
  let msg = Printf.sprintf "Writing log to \"file:%s\"." path in
  Feedback.msg_notice (Pp.str msg)
