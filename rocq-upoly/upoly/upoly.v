(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export skylabs.upoly.base.	(* base.v *)

(** Types *)

Require skylabs.upoly.UTypes.	(* UTypes.v *)
Require skylabs.upoly.prod.	(* prod.v *)
Require skylabs.upoly.sum.	(* sum.v *)
Require skylabs.upoly.option.	(* option.v *)
Require skylabs.upoly.list.	(* list.v *)

(** Monads *)

Require skylabs.upoly.id.	(* id.v *)
Require skylabs.upoly.trace.	(* trace.v *)
Require skylabs.upoly.reader.	(* reader.v *)
Require skylabs.upoly.writer.	(* writer.v *)
Require skylabs.upoly.state.	(* state.v *)

(** Monad transformers *)

Require skylabs.upoly.optionT.	(* optionT.v *)
Require skylabs.upoly.listT.	(* listT.v *)
Require skylabs.upoly.traceT.	(* traceT.v *)
Require skylabs.upoly.readerT.	(* readerT.v *)
Require skylabs.upoly.writerT.	(* writerT.v *)
Require skylabs.upoly.stateT.	(* stateT.v *)

Require Export skylabs.upoly.effects.	(* effects.v *)
