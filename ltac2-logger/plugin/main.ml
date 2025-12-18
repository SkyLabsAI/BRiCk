(*
 * Copyright (C) 2021 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

open Ltac2_plugin
open Stdlib_extra.Extra
open Logger_lib.Logger
open Tac2ffi
open Tac2expr
open Tac2externals

(* Registering hooks for timing and instruction counts in spans. *)
let _ =
  (* Check that instruction counts fit on native integers. *)
  if Sys.word_size != 64 then assert false;
  let start_hook s =
    let update metadata =
      let t0 = Time.Monotonic.(in_mus (now ())) in
      let metadata = Metadata.make_int Fun.id "t0" t0 :: metadata in
      match Instr.read_counter () with
      | Ok(c0) -> Metadata.make_int Int64.to_int "c0" c0 :: metadata
      | Error(_) -> metadata
    in
    Span.update_metadata s update
  in
  let end_hook s =
    let update metadata =
      let t0 = Time.Monotonic.(in_mus (now ())) in
      let metadata = Metadata.make_int Fun.id "t1" t0 :: metadata in
      match Instr.read_counter () with
      | Ok(c0) -> Metadata.make_int Int64.to_int "c1" c0 :: metadata
      | Error(_) -> metadata
    in
    Span.update_metadata s update
  in
  Span.set_start_span_hook start_hook;
  Span.set_end_span_hook end_hook;
  let get_log_direct_printing : unit -> bool =
    let key = ["SL"; "Direct"; "Log"] in
    let getter = Goptions.declare_bool_option_and_ref ~key ~value:false () in
    getter.Goptions.get
  in
  Event.set_direct_printing get_log_direct_printing

let reset_log : unit -> unit =
  let initial_state = Log.State.save () in
  fun () -> Log.State.restore initial_state

(* Registering a hook for outputing the log to a file at process exit. *)
let _ =
  let warn_bad_log : Pp.t -> unit =
    let warning : CWarnings.warning =
      let name = "sl-ill-formed-log" in
      let default = CWarnings.Enabled in
      CWarnings.create_warning ~name ~default ()
    in
    CWarnings.create_in warning (fun x -> x) ?loc:None ?quickfix:None
  in
  match Sys.getenv_opt "SL_LOG_FILE" with None -> () | Some(file) ->
  let hook () =
    try
      try Log.write file with Failure(msg) ->
      let msg = Format.sprintf "Ill-formed log (%s), using debug mode." msg in
      warn_bad_log (Pp.str msg);
      Log.write ~debug:true file
    with Sys_error(msg) ->
      let msg =
        Format.sprintf "Could not write the log to %S (%s)\n%!" file msg
      in
      warn_bad_log (Pp.str msg)
  in
  Stdlib.at_exit hook

let define s = define { mltac_plugin = "sl.log"; mltac_tactic = s }

let unit_valexpr : Tac2val.valexpr = Tac2ffi.of_unit ()

(* Log event recording *)

let fmt = Tac2extffi.format

let _ =
  define "log" (Flags.repr @-> int @-> fmt @-> tac valexpr) @@ fun flag level fn ->
  let enabled = Flags.enabled flag level in
  let metadata = [Flags.log_flag flag; Flags.log_level level] in
  let log =
    let module M =
      struct
        type t = Ltac2_format.msg

        let pp : t Format.pp = fun ff m ->
          Format.pp_print_string ff (Ltac2_format.msg_to_string m)

        let to_json : t -> JSON.t = fun m ->
          let s = Ltac2_format.msg_to_string m in
          let (header, data) =
            match String.index_opt s '\n' with
            | Some(i) when i > 0 && s.[i - 1] = ':' ->
                (Some(String.take i s), String.drop (i + 1) s)
            | _                                     ->
                (None, s)
          in
          let data = `String(data) in
          match header with
          | None    -> data
          | Some(h) -> `Assoc([("header", `String(h)); ("data", data)])
      end
    in
    Event.make_recorder (module M) ~metadata
  in
  Ltac2_format.eval ~enabled log fn

(* Message and related pretty-printing primitives *)

let _ = define "msg" (fmt @-> tac valexpr) Ltac2_format.eval_msg

let _ =
  let open Ltac2_format in
  define "pp_ast" (valexpr @-> constr @-> ret msg_repr) @@ fun _ c ->
  [Ast(c)]

let _ =
  let open Ltac2_format in
  define "pp_message" (valexpr @-> pp @-> ret msg_repr) @@ fun _ m ->
  [Pp(m)]

let _ =
  let open Ltac2_format in
  define "pp_err" (valexpr @-> err @-> ret msg_repr) @@ fun _ e ->
  [Pp(CErrors.iprint e)]

let _ =
  let open Ltac2_format in
  define "pp_list"
    (closure @-> valexpr @-> list valexpr @-> tac msg_repr) @@ fun pp _ xs ->
  let open Proofview.Notations in
  let rec eval acc xs =
    match xs with
    | []      -> Proofview.tclUNIT [Msg(List.rev acc)]
    | x :: xs ->
        Tac2val.apply pp [unit_valexpr; x] >>= fun m ->
        let m = Tac2ffi.to_ext Ltac2_format.msg_tag m in
        eval (Ltac2_format.Msg(m) :: acc) xs
  in
  eval [] xs

(* Log spans primitives *)

let span_tag : Span.t Tac2dyn.Val.tag =
  Tac2dyn.Val.create "span"

let span : Span.t Tac2ffi.repr = Tac2ffi.repr_ext span_tag

let _ =
  define "push_span" (string @-> tac span) @@ fun name ->
  let f () = Span.push name in
  Proofview.(tclLIFT (NonLogical.make f))

let _ =
  define "pop_span" (span @-> tac bool) @@ fun span ->
  let f () = try Span.pop span; true with Failure(_) -> false in
  Proofview.(tclLIFT (NonLogical.make f))

let _ =
  define "pop_span_until" (span @-> tac bool) @@ fun span ->
  let f () =
    let state = Log.State.save () in
    try Span.pop_until span; true with Failure(_) ->
      Log.State.restore state; false
  in
  Proofview.(tclLIFT (NonLogical.make f))

let _ =
  define "pop_all_spans" (unit @-> tac unit) @@ fun () ->
  let f () = Span.pop_all () in
  Proofview.(tclLIFT (NonLogical.make f))

let _ =
  define "add_span_metadata_int"
    (span @-> string @-> int @-> tac unit)
    @@ fun span k v ->
  let f () =
    let data = Metadata.make_int Fun.id k v in
    Span.update_metadata span (fun metadata -> data :: metadata)
  in
  Proofview.(tclLIFT (NonLogical.make f))

let _ =
  define "add_span_metadata_string"
    (span @-> string @-> string @-> tac unit)
    @@ fun span k v ->
  let f () =
    let data = Metadata.make_string Fun.id k v in
    Span.update_metadata span (fun metadata -> data :: metadata)
  in
  Proofview.(tclLIFT (NonLogical.make f))

(* Log level query primitives *)

let _ =
  define "log_enabled" (Flags.repr @-> int @-> tac bool) @@ fun flag i ->
  let f () = Flags.enabled flag i in
  Proofview.(tclLIFT (NonLogical.make f))

let _ =
  define "log_level" (Flags.repr @-> tac int) @@ fun flag ->
  let f () = Flags.get_level flag in
  Proofview.(tclLIFT (NonLogical.make f))

(* Log output primitives *)

let _ =
  define "output_log"
    (bool @-> option string @-> tac unit) @@ fun debug target ->
  let f () =
    try Output.output_log debug target with Failure(msg) ->
      Feedback.msg_warning (Pp.str msg)
  in
  Proofview.(tclLIFT (NonLogical.make f))

let _ =
  define "output_log_tmp" (bool @-> string @-> tac unit) @@ fun debug ext ->
  let f () =
    try Output.output_log_tmp debug ext with Failure(msg) ->
      Feedback.msg_warning (Pp.str msg)
  in
  Proofview.(tclLIFT (NonLogical.make f))


(* Log state primitives *)

let _ =
  define "reset_log" (unit @-> tac unit) @@ fun () ->
  Proofview.(tclLIFT (NonLogical.make reset_log))

let log_state_tag : Log.State.t Tac2dyn.Val.tag =
  Tac2dyn.Val.create "log_state"

let state : Log.State.t Tac2ffi.repr =
  Tac2ffi.repr_ext log_state_tag

let _ =
  define "save_log_state" (unit @-> tac state) @@ fun () ->
  Proofview.(tclLIFT (NonLogical.make Log.State.save))

let _ =
  define "restore_log_state" (state @-> tac unit) @@ fun s ->
  let f () = Log.State.restore s in
  Proofview.(tclLIFT (NonLogical.make f))

(* Coq output primitives *)

let buffer_tag : Coq_output.buffer Tac2dyn.Val.tag =
  Tac2dyn.Val.create "Coq_output.buffer"

let buffer : Coq_output.buffer Tac2ffi.repr =
  Tac2ffi.repr_ext buffer_tag

let _ =
  define "Coq_output.start_capture"
    (unit @-> tac buffer) @@ fun () ->
  Proofview.(tclLIFT (NonLogical.make Coq_output.start_capture))

let _ =
  define "Coq_output.contents" (buffer @-> tac string) @@ fun b ->
  let f () = Coq_output.contents b in
  Proofview.(tclLIFT (NonLogical.make f))


let _ =
  define "Coq_output.clear" (buffer @-> tac unit) @@ fun b ->
  let f () = Coq_output.clear b in
  Proofview.(tclLIFT (NonLogical.make f))

let _ =
  define "Coq_output.end_capture" (buffer @-> tac unit) @@ fun b ->
  let f () = Coq_output.end_capture b in
  Proofview.(tclLIFT (NonLogical.make f))
