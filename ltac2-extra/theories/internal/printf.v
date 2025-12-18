(*
 * Copyright (C) 2021-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.init.

(** Minor extensions to [Ltac2.Printf] *)
Module Printf.
  Import Ltac2 Init.
  Export Ltac2.Printf.

  (** Note: The following pretty-printers for base Ltac2 types are tied to
      Ltac2's feedback-oriented printf, fprintf and won't work with the
      logger. We plan to unify things in the future. Specifically,
      ltac2_extensions will exposes a `kfprintf` primitive and this module
      will use that to *replace* Ltac2's printf, fprintf. After those
      changes, all formatting can use the logger's enhanced format strings,
      and all pretty-printing functions can work for both feedback and
      logging. *)

  (** [Import Printf.Notations] pulls in less than [Import Printf], which
      can be useful for code that wants to print but doesn't want a cluttered
      Ltac2 environment. *)
  Module Export Notations.
    Ltac2 Notation "printf" fmt(format) := Printf.printf fmt.
    Ltac2 Notation "fprintf" fmt(format) := Printf.fprintf fmt.
  End Notations.

  Ltac2 pp_string : string pp := fun _ => Message.of_string.
  Ltac2 pp_int : int pp := fun _ => Message.of_int.
  Ltac2 pp_ident : ident pp := fun _ => Message.of_ident.
  Ltac2 pp_constr : constr pp := fun _ => Message.of_constr.
  Ltac2 pp_exn : exn pp := fun _ => Message.of_exn.
  Ltac2 pp_message : message pp := fun _ msg => msg.
  Ltac2 pp_bool : bool pp := fun _ b =>
    Message.of_string (if b then "true" else "false").

  Ltac2 pp_option : 'a pp -> 'a option pp := fun pp _ m =>
    match m with
    | Some x => fprintf "(Some %a)" pp x
    | None => Message.of_string "None"
    end.

  Ltac2 pp_list_sep : string -> 'a pp -> 'a list pp := fun sep pp () xs =>
    let sep := Message.of_string sep in
    let rec loop xs (acc : message list) :=
      match xs with
      | [] => acc
      | x :: xs =>
        let x := pp () x in
        match xs with
        | [] => x :: acc
        | _ :: _ => loop xs (sep :: x :: acc)
        end
      end
    in
    let msgs := loop xs [] in
    let msgs := List.rev msgs in
    List.fold_left Message.concat (Message.of_string "") msgs.
  Ltac2 pp_list : 'a pp -> 'a list pp := fun pp _ xs =>
    fprintf "[%a]" (pp_list_sep "; " pp) xs.

  Ltac2 pp_name : name pp := fun _ mid =>
    let name :=
      match mid with
      | Some id => Ident.to_string id
      | None => "_"
      end
    in
    Message.of_string name.

  Ltac2 pp_binder : binder pp := fun _ b =>
    let name := Constr.Binder.name b in
    let ty := Constr.Binder.type b in
    fprintf "%a : %t" pp_name name ty.

  Ltac2 pp_reference : Std.reference pp := fun _ r =>
    let ids := Env.path r in
    pp_list_sep "." pp_ident () ids.

  (** Just enough info to know what case you forgot. *)
  Ltac2 pp_kind_tag : Constr.Unsafe.kind pp := fun _ k =>
    let s :=
      match k with
      | Constr.Unsafe.Rel _ => "Rel"
      | Constr.Unsafe.Var _ => "Var"
      | Constr.Unsafe.Meta _ => "Meta"
      | Constr.Unsafe.Evar _ _ => "Evar"
      | Constr.Unsafe.Sort _ => "Sort"
      | Constr.Unsafe.Cast _ _ _ => "Cast"
      | Constr.Unsafe.Prod _ _ => "Prod"
      | Constr.Unsafe.Lambda _ _ => "Lambda"
      | Constr.Unsafe.LetIn _ _ _ => "LetIn"
      | Constr.Unsafe.App _ _ => "App"
      | Constr.Unsafe.Constant _ _ => "Constant"
      | Constr.Unsafe.Ind _ _ => "Ind"
      | Constr.Unsafe.Constructor _ _ => "Constructor"
      | Constr.Unsafe.Case _ _ _ _ _ => "Case"
      | Constr.Unsafe.Fix _ _ _ _ => "Fix"
      | Constr.Unsafe.CoFix _ _ _ => "CoFix"
      | Constr.Unsafe.Proj _ _ _ => "Proj"
      | Constr.Unsafe.Uint63 _ => "Uint63"
      | Constr.Unsafe.Float _ => "Float"
      | Constr.Unsafe.String _ => "String"
      | Constr.Unsafe.Array _ _ _ _ => "Array"
      end
    in Message.of_string s.

End Printf.
