(*
 * Copyright (C) 2023 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.extra.

Declare ML Module "ltac2-logger.plugin".

(** Capturing the default Coq output into a buffer. *)
Module Coq_output.
  Import Ltac2.

  Ltac2 Type buffer.

  Ltac2 @external start_capture : unit -> buffer :=
    "br.log" "Coq_output.start_capture".

  Ltac2 @external contents : buffer -> string :=
    "br.log" "Coq_output.contents".

  Ltac2 @external clear : buffer -> unit :=
    "br.log" "Coq_output.clear".

  Ltac2 @external end_capture : buffer -> unit :=
    "br.log" "Coq_output.end_capture".
End Coq_output.

(* Noisy tests
Import Printf.
Ltac2 Eval (
  let b := Coq_output.start_capture () in
  printf "Scratch that!";
  Coq_output.clear b;
  printf "Hello to the buffer!";
  printf "Even more text!";
  let s := Coq_output.contents b in
  Coq_output.end_capture b;
  printf "Captured output: [%s]" s
).
*)

(** Logging support. *)
Module Log.
  Import Ltac2.

  (** Type of a raw (not yet rendered) log message in OCaml *)
  Ltac2 Type msg.

  (** Flag attached to a log entry: should morally be abstract, so don't
      construct values yourself. *)
  Ltac2 Type log_flag := int.

  (** Log level for a log entry. A log entry with level 0 or less is always
      added to the log, irrespective of the currently set logging level. It
      cannot be disabled. *)
  Ltac2 Type log_level := int.

  (** [log_enabled flag level] indicates whether the logging is enabled for a
      message with the given [flag] and [level]. *)
  Ltac2 @ external log_enabled : log_flag -> log_level -> bool :=
    "br.log" "log_enabled".

  (** [log_level flag] returns the currently set log level for messages with
      the given [flag]. *)
  Ltac2 @ external log_level : log_flag -> log_level :=
    "br.log" "log_level".

  (** [log_msg flag level format ...] logs the message described by [fmt] and
      the following arguments, provided that the function is fully applied. A
      [flag] and [level] are attached to the log entry. NOTE: this function
      cannot be called directly since a notation is required to recognise the
      [format] argument as a format string. *)
  Ltac2 @ external log_msg : log_flag -> log_level -> ('a, unit, msg, unit) format -> 'a :=
    "br.log" "log".

  (** [msg_msg fmt ...] interprets the given format and arguments as would the
      [log_msg] function, but it returns the [msg] at the end. The aim of this
      function is to be used in combination with the ["%a"] format. NOTE: this
      function cannot be called directly (see [log_msg] above). *)
  Ltac2 @ external msg_msg : ('a, unit, msg, msg) format -> 'a :=
    "br.log" "msg".

  Module Notations.
    (** Generic notation for calling [log_msg]. *)
    Ltac2 Notation "log[" flag(tactic(0)) "," level(tactic(0)) "]" fmt(format) :=
      log_msg flag level fmt.

    (** Notation for calling [msg_msg] to create a message using a format. *)
    Ltac2 Notation "msg!" fmt(format) :=
      msg_msg fmt.

    Ltac2 Dev Log Flag tac.
  End Notations.
  Import Notations.

  (** Printer for messages. *)
  Ltac2 @ external pp_message : unit -> message -> msg :=
    "br.log" "pp_message".

  Ltac2 @ external pp_err : unit -> err -> msg :=
    "br.log" "pp_err".

  Ltac2 @ external pp_ast : unit -> constr -> msg :=
    "br.log" "pp_ast".

  Ltac2 @ external pp_list : (unit -> 'a -> msg) -> unit -> 'a list -> msg :=
    "br.log" "pp_list".

  Ltac2 pp_exn (_ : unit) (e : exn) : msg :=
    msg! "%a" pp_message (Message.of_exn (Control.clear_exn_info e)).

  Ltac2 pp_bool : unit -> bool -> msg := fun _ b =>
    if b then msg! "true" else msg! "false".

  Ltac2 pp_int : unit -> int -> msg := fun _ i =>
    msg! "%i" i.

  Ltac2 pp_option : (unit -> 'a -> msg) -> unit -> 'a option -> msg := fun f _ o =>
    match o with
    | None   => msg! "None"
    | Some v => msg! "Some(%a)" f v
    end.

  (* TODO: move somewhere else? *)
  Ltac2 Notation "if!" cond(self) "then" run(thunk(tactic(5))) :=
    if cond then run () else ().

  (** Log spans. *)
  Module Span.
    (** Type of a span. *)
    Ltac2 Type t.

    (** [push_span name] opens a new span named [name], and returns it. *)
    Ltac2 @ external push : string -> t :=
      "br.log" "push_span".

    (** [try_pop s] closes the span [s], and then returns a boolean indicating
        whether it was successful. If it fails, the state of the logger is
        unchanged. *)
    Ltac2 @ external try_pop : t -> bool :=
      "br.log" "pop_span".

    (** [try_pop_until s] is similar to [try_pop s], but may close other spans
        before [s]. *)
    Ltac2 @ external try_pop_until : t -> bool :=
      "br.log" "pop_span_until".

    (** [pop_all ()] closes all open spans. Avoid using this function, as this
        may break compositionality. *)
    Ltac2 @ external pop_all : unit -> unit :=
      "br.log" "pop_all_spans".

    (** Exception raised by [pop] and [pop_until] if they fail. *)
    Ltac2 Type exn ::= [ Pop_error ].

    Ltac2 pop : t -> unit := fun s =>
      if try_pop s then () else Control.zero Pop_error.

    Ltac2 pop_until : t -> unit := fun s =>
      if try_pop_until s then () else Control.zero Pop_error.

    (** [mpush name] is similar to [push name], but it also works when there
        are several (or no) focused goals. *)
    Ltac2 mpush name := Control.without_focus (fun () => push name).

    (** [mpop span] is similar to [pop span], but it also works when there are
        several (or no) focused goals. *)
    Ltac2 mpop span := Control.without_focus (fun () => pop span).

    (** [mpop_until span] is similar to [pop_until span], but it also works
        when there are several (or no) focused goals. *)
    Ltac2 mpop_until span := Control.without_focus (fun () => pop_until span).

    Ltac2 with_span_aux (notify : bool) (name : string) (tac : unit -> 'a) : 'a :=
      let rec go tac :=
        let span := push name in
        match Control.case_bt tac with
        | Control.Val_bt (res, handle) =>
          pop span;
          Control.plus (fun () => res) (fun e => go (fun () => handle e))
        | Control.Err_bt e bt =>
          if! notify then
            log[tac] "Exception caught by [with_span '%s']" name;
            pop_until span;
          if! notify then
            log[tac] "[with_span '%s'] raised an exception:\n%a" name pp_exn e;
          Control.zero_bt e bt
        end
      in
      go tac.

    Ltac2 with_span_ notify name tac := once (with_span_aux notify name tac).
    Ltac2 with_span name tac := once (with_span_ true name tac).

    Ltac2 mwith_span_aux (notify : bool) (name : string) (tac : unit -> 'a) : 'a :=
      let rec go tac :=
        let span := push name in
        match Control.case_bt tac with
        | Control.Val_bt (res, handle) =>
          mpop span;
          Control.plus (fun () => res) (fun e => go (fun () => handle e))
        | Control.Err_bt e bt =>
          let log_and_pop () :=
            if! notify then
              log[tac] "Exception caught by [mwith_span '%s']" name;
            mpop_until span;
            if! notify then
              log[tac] "[mwith_span '%s'] raised an exception:\n%a" name pp_exn e
          in
          Control.without_focus log_and_pop;
          Control.zero e bt
        end
      in
      go tac.

    (** [mwith_span name tac] is similar to [with_span name tac], but it also
        works when there are several (or no) focused goals. *)
    Ltac2 mwith_span_ notify name tac := once (mwith_span_aux notify name tac).
    Ltac2 mwith_span name tac := once (mwith_span_ true name tac).
    Ltac2 mwith_span_backtracking name tac := mwith_span_ true name tac.

    (** [add_int_metadata s k v] sets the metadata field [k] of span [s] to be
        the integer value [v]. *)
    Ltac2 @ external add_int_metadata : t -> string -> int -> unit :=
      "br.log" "add_span_metadata_int".

    (** [add_string_metadata s k v] sets the metadata field [k] of span [s] to
        be the string value [v]. *)
    Ltac2 @ external add_string_metadata : t -> string -> string -> unit :=
      "br.log" "add_span_metadata_string".

    (** [with_status name tac] runs the tactic surrounded by the span and appends
        '+success' or '+failure' to log whether [tac] succeeded or failed. *)
    Ltac2 with_status name tac :=
      let span := Log.Span.push name in
      let run () :=
        let res := tac () in
        Log.Span.add_string_metadata span "status" "success";
        Log.Span.pop span; res
      in
      let handle e bt :=
        let log_and_pop () :=
          Log.Span.add_string_metadata span "status" "failure";
          log[tac] "[mwith_span '%s'] raised an exception:\n%a" name Log.pp_exn e;
          Log.Span.pop_until span
        in
        Control.without_focus log_and_pop;
        Control.zero_bt e bt
      in
      Control.once_plus_bt run handle.

    (** same as [with_status] but supports multiple goals. *)
    Ltac2 mwith_status name tac :=
      let span := Log.Span.mpush name in
      let run () :=
        let res := tac () in
        Log.Span.add_string_metadata span "status" "success";
        Log.Span.mpop span; res
      in
      let handle e bt :=
        let log_and_pop () :=
          Log.Span.add_string_metadata span "status" "failure";
          log[tac] "[mwith_span '%s'] raised an exception:\n%a" name Log.pp_exn e;
          Log.Span.mpop_until span
        in
        Control.without_focus log_and_pop;
        Control.zero_bt e bt
      in
      Control.once_plus_bt run handle.
  End Span.

  (** Internal logger state manipulation. *)
  Module State.
    Ltac2 Type t.

    Ltac2 @ external save : unit -> t :=
      "br.log" "save_log_state".

    Ltac2 @ external restore : t -> unit :=
      "br.log" "restore_log_state".
  End State.

  (** Reset the log state. *)
  Ltac2 @ external reset_log : unit -> unit :=
    "br.log" "reset_log".

  (** [output_log_generic debug file] outputs the accumulated log to the given
      [file], if any. Otherwise the log is printed to the Coq buffer (notice).
      The [debug] flag controls the behavior on logs that have unclosed spans.
      If [debug] is false, an error is printed instead of the log. If [debug]
      is true, the partial log is printed. *)
  Ltac2 @ external output_log_generic : bool -> string option -> unit :=
    "br.log" "output_log".

  (** [output_log_tmp debug ext] outputs the accumulated log to a temporary
      file with extension [ext]. The [debug] argument is handled exactly as in
      function [output_log_generic]. *)
  Ltac2 @ external output_log_tmp : bool -> string -> unit :=
    "br.log" "output_log_tmp".

  Ltac2 output_log () := output_log_generic false None.
  Ltac2 output_log_debug () := output_log_generic true None.
  Ltac2 output_log_file file := output_log_generic false (Some file).
  Ltac2 output_log_file_debug file := output_log_generic true (Some file).

  Ltac2 Type exn ::= [ WithLogError(string, exn) ].

  Ltac2 with_log (debug : bool) (file : string option) (tac : unit -> unit) :=
    Control.without_focus reset_log;
    let run () :=
      Control.enter tac;
      Control.without_focus (fun () => output_log_generic debug file)
    in
    let handle e :=
      let log_and_output () :=
        log[tac] "Exception caught by 'with_log':\n%a" pp_exn e;
        if! Bool.neg debug then log[tac] "Forcing debug mode for 'with_log'";
        output_log_generic true file (* Use debug mode to avoid problems. *)
      in
      Control.without_focus log_and_output;
      let msg :=
        match file with
        | None   => "PREFIX YOUR TACTIC WITH 'Fail' TO SEE LOG OUTPUT"
        | Some _ => "YOUR FILE WAS WRITTEN"
        end
      in
      Control.zero (WithLogError msg e)
    in
    Control.plus run handle.

  Ltac2 with_log_tmp (debug : bool) (ext : string) (tac : unit -> unit) :=
    Control.without_focus reset_log;
    let run () :=
      Control.enter tac;
      Control.without_focus (fun () => output_log_tmp debug ext)
    in
    let handle e :=
      let log_and_output () :=
        log[tac] "Exception caught by 'with_log':\n%a" pp_exn e;
        if! Bool.neg debug then log[tac] "Forcing debug mode for 'with_log'";
        output_log_tmp true ext (* Use debug mode to avoid problems. *)
      in
      Control.without_focus log_and_output;
      let msg := "PREFIX YOUR TACTIC WITH 'Fail' TO SEE LOG OUTPUT" in
      Control.zero (WithLogError msg e)
    in
    Control.plus run handle.

  Module Ltac1.
    Ltac2 parse_debug (debug : Ltac1.t) : bool :=
      match Ltac1.to_bool debug with
      | Some debug => debug
      | None       => throw_invalid! "not a concrete [bool]"
      end.

    Ltac2 parse_ofile (ofile : Ltac1.t) : string option :=
      match Ltac1.to_option String.of_string_constr ofile with
      | Some ofile => ofile
      | None       => throw_invalid! "not a concrete [option string]"
      end.

    Ltac2 parse_ext (ext : Ltac1.t) : string :=
      match Ltac1.to_string ext with
      | Some ext => ext
      | None     => throw_invalid! "not a concrete [string]"
      end.

    Ltac2 output_log_generic (debug : Ltac1.t) (ofile : Ltac1.t) : unit :=
      let debug := parse_debug debug in
      let ofile := parse_ofile ofile in
      output_log_generic debug ofile.

    Ltac2 with_log (debug : Ltac1.t) (ofile : Ltac1.t) (tac : Ltac1.t) :=
      let debug := parse_debug debug in
      let ofile := parse_ofile ofile in
      with_log debug ofile (fun () => Ltac1.run tac).

    Ltac2 output_log_tmp (debug : Ltac1.t) (ext : Ltac1.t) : unit :=
      let debug := parse_debug debug in
      let ext := parse_ext ext in
      output_log_tmp debug ext.

    Ltac2 with_log_tmp (debug : Ltac1.t) (ext : Ltac1.t) (tac : Ltac1.t) :=
      let debug := parse_debug debug in
      let ext := parse_ext ext in
      with_log_tmp debug ext (fun () => Ltac1.run tac).
  End Ltac1.

  Module Ltac1Notations.
    Import Ltac1.
    (** * Ltac1 Logging tactics *)

    (** The following tactics can be used for logging. Note that logging is only
        recorded according to the value of the [BR Debug] Coq variable. It can be
        read with [Test BR Debug], set with [Set BR Debug "..."], and reset using
        [Unset BR Debug]. Here are common examples of values for the option:
        - [Set BR Debug "@default=1"] is useful for user-level debugging, in case
          you only care about successful hint applications. You can also use the
          character [_] as a shortcut for [@default].
        - [Set BR Debug "@default=3"] is similarly useful, but includes failures.
        - [Set BR Debug "@all=10"] sets all debugging levels to maximum. You can
          also use character [*] as a shortcut for [@all].
        - [Set BR Debug "@all=3,ocaml=6"] is similar but corrects a level.

        Note that when logging is enabled, any run of the above tactics will have
        the side-effect of adding log entries. In particular, if you step back in
        a proof, and re-run a tactic, then the logging will be registered twice.

        To mitigate this issue, we provide the [with_log* tac] family of tactics,
        that can be used to generate a log for the given tactic [tac]. This means
        that you can use [with_log go] to generate the log for a single call to
        the [go] tactic.

        LIMITATION: the [output_log*] tactics won't work right before a [Qed], at
        the end of the proof (i.e., when there are no goals). As a workaround you
        can use [all: output_log.], or similarly for other variants. *)

    Import Strings.String.

    (** [reset_log] resets the state of the logger. *)
    #[global] Tactic Notation "reset_log" :=
      ltac2:(Log.reset_log ()).

    (** [pop_all_spans] closes all currently open spans. This is useful when a
        function doing logging is interrupted by, e.g., [Timeout]. *)
    #[global] Tactic Notation "pop_all_spans" :=
      ltac2:(Log.Span.pop_all ()).

    (** [output_log_generic debug ofile] outputs the accumulated log messages. The
        [debug] parameter is expected to be a concrete Coq boolean, and it decides
        whether the log should be printed when incomplete (i.e., if not all spans
        are closed). The [ofile] parameter is expected to be a Coq option holding
        a Coq string, and it gives an optional (absolute) file path where to write
        the log. If no file is specified ([None] constructor), then the output is
        sent to the Coq buffer at the "notice" level. *)
    #[global] Tactic Notation "output_log_generic" constr(debug) constr(ofile) :=
      let run :=
        ltac2:(debug ofile |- Log.Ltac1.output_log_generic debug ofile)
      in
      run debug ofile.

    #[global] Tactic Notation "output_log"  :=
      output_log_generic false (@None string).
    #[global] Tactic Notation "output_log!" :=
      output_log_generic true  (@None string).

    #[global] Tactic Notation "output_log_file"  constr(file) :=
      output_log_generic false (@Some string file).
    #[global] Tactic Notation "output_log_file!" constr(file) :=
      output_log_generic true  (@Some string file).

    (** [with_log_generic debug ofile tac] resets the logger, runs [tac], and then
        outputs the log as if [output_log_generic debug ofile] was called. *)
    #[global] Tactic Notation "with_log_generic" constr(debug) constr(ofile) tactic(tac) :=
      let run :=
        ltac2:(debug ofile tac |- Log.Ltac1.with_log debug ofile tac)
      in
      run debug ofile tac.

    #[global] Tactic Notation "with_log"  tactic(tac) :=
      with_log_generic false (@None string) tac.
    #[global] Tactic Notation "with_log!" tactic(tac) :=
      with_log_generic true  (@None string) tac.

    #[global] Tactic Notation "with_log_file"  constr(file) tactic(tac) :=
      with_log_generic false (@Some string file) tac.
    #[global] Tactic Notation "with_log_file!" constr(file) tactic(tac) :=
      with_log_generic true  (@Some string file) tac.


    (** [output_log_generic debug ofile] outputs the accumulated log messages. The
        [debug] parameter is expected to be a concrete Coq boolean, and it decides
        whether the log should be printed when incomplete (i.e., if not all spans
        are closed). The [ext] parameter is expected to be a concrete Coq string,
        and it specifies the extension of the temporary file that the log will be
        written to. The name of the used temporary file is sent to the Coq buffer
        at the "notice" level. *)
    #[global] Tactic Notation "output_log_tmp" constr(debug) constr(ext) :=
      let run :=
        ltac2:(debug ext |- Log.Ltac1.output_log_tmp debug ext)
      in
      run debug ext.

    #[global] Tactic Notation "output_log_tmp_file"  constr(ext) :=
      output_log_tmp false ext.
    #[global] Tactic Notation "output_log_tmp_file!" constr(ext) :=
      output_log_tmp true  ext.

    (** [with_log_tmp debug ext tac] resets the logger, runs [tac], and then
        outputs the log as if [output_log_tmp debug ext] was called. *)
    #[global] Tactic Notation "with_log_tmp" constr(debug) constr(ext) tactic(tac) :=
      let run :=
        ltac2:(debug ext tac |- Log.Ltac1.with_log_tmp debug ext tac)
      in
      run debug ext tac.

    #[global] Tactic Notation "with_log_tmp_file"  constr(ext) tactic(tac) :=
      with_log_tmp false ext tac.
    #[global] Tactic Notation "with_log_tmp_file!" constr(ext) tactic(tac) :=
      with_log_tmp true  ext tac.
  End Ltac1Notations.
End Log.
Export Log.Notations.
