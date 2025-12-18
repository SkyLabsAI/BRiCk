(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.plugin.
Require Import skylabs.ltac2.extra.internal.init.
Require Import skylabs.ltac2.extra.internal.constr.
Require Import skylabs.ltac2.extra.internal.std.

(** Minor extensions to [Ltac2.Ident] *)
(**
This is part of [skylabs.prelude.tactics.ltac2]. [Require] that,
instead.
*)

Module Ident.
  Import Ltac2 Constr Constr.Unsafe.
  Export Ltac2.Ident.

  (**
  <<Rep (fun id => tt)>> represents identifier <<id>> in Gallina
  *)
  Variant rep : Set := Rep (_ : unit -> unit).

  Register rep as skylabs.ltac2.extra.Ident.rep.type.
  Register Rep as skylabs.ltac2.extra.Ident.rep.Rep.

  Ltac2 invalid_arg (whence : string) (t : constr) : 'a :=
    let m := Message.of_string whence in
    let m := Message.concat m (Message.of_string ": ") in
    let m := Message.concat m (Message.of_constr t) in
    Control.throw (Invalid_argument (Some m)).

  Ltac2 of_rep_opt : constr -> ident option := fun t =>
    lazy_match! Std.eval_whd_all t with
    | Rep ?f =>
      let (b, _) := Destruct.of_lambda f in
      let (n, _, _) := Binder.deconstruct b in
      n
    | ?t => invalid_arg "Ident.of_rep_opt: Expected <<Ident.rep>> constructor" t
    end.

  Ltac2 of_rep : constr -> ident := fun t =>
    match of_rep_opt t with
    | Some id => id
    | None => invalid_arg "Ident.of_rep: No name hint" t
    end.

  Ltac2 as_rep' () : ident -> constr :=
    let unit := constr:(unit) in
    let tt := constr:(tt) in
    let rep := constr:(Rep) in
    fun id =>
    let b := Binder.unsafe_make (Some id) Binder.Relevant unit in
    make_app1 rep (make_lambda b tt).
  Ltac2 as_rep (id : ident) : constr := as_rep' () id.

End Ident.
