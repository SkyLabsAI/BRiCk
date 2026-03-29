(*
 * Copyright (C) 2026 SkyLabs AI, Inc.
 *)
Require Import Ltac2.Ltac2.
Require Import Ltac2.Control.
Require Import Ltac2.Printf.


Require Import Ltac2.Std.
Require Import Stdlib.Strings.PrimString.
Require Import skylabs.ltac2.extra.extra.

Declare ML Module "ltac2-tc-dispatch.plugin".

(* The typeclass: P is the goal/type, path is the module hierarchy, name is the tactic *)
Class Ltac2Lookup (P : Prop) := {
    ltac2_path : list string;
    ltac2_name : string;
  }.

Module ltac2.

  Ltac2 @ external resolve_ltac2 : string list -> string -> (unit -> unit) option :=
    "ltac2_tc_dispatch" "resolve_ltac2".

  Ltac2 Type exn ::= [ UnexpectedConstr (string * constr) ].

  Ltac2 string_of_pstring_constr (c : constr) : string :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.String s => Pstring.to_string s
    | _ => throw (UnexpectedConstr("Expected a pstring", c))
    end.

  Ltac2 rec list_of_list_constr (f : constr -> 'a) (c : constr) : 'a list :=
    lazy_match! c with
    | List.nil => []
    | List.cons ?c ?cs => f c :: list_of_list_constr f cs
    end.

  Ltac2 goal_dispatch_with (dbs : ident list option) :=
    let g := Control.goal () in
    let query := constr:(Ltac2Lookup $g) in
    (* let _ := printf "query=%t" query in *)
    let inst := Constr.Unsafe.make (TC.resolve dbs query) in
    (* let _ := printf "inst=%t" inst in *)
    let flags := RedFlags.all in
    let reduced_inst := Std.eval_cbv flags inst in
    (* let _ := printf "reduced_inst=%t" reduced_inst in *)

    lazy_match! reduced_inst with
    | {| ltac2_path := ?p; ltac2_name := ?n |} =>
        let p_ltac2 := list_of_list_constr (fun c => string_of_pstring_constr c) p in
        let n_ltac2 := string_of_pstring_constr n in
        (* printf "n_ltac2=%s" n_ltac2 ; *)

        match resolve_ltac2 p_ltac2 n_ltac2 with
        | Some f =>
            (* let _ := printf "resolve_ltac2 success!" in *)
            f ()
        | None =>
            (* let _ := printf "resolve_ltac2 failed!" in *)

            let err :=
              Message.concat [Message.of_string "Could not find: ";
                              Message.of_string n_ltac2] in
            Control.zero (Tactic_failure (Some err))
        end
    | _ =>
        Control.zero (Tactic_failure (Some (Message.of_string "Could not reduce instance to record.")))
    end.

End ltac2.

Ltac goal_dispatch :=
  idtac;
  ltac2:(ltac2.goal_dispatch_with None).
