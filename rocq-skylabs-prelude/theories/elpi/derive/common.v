(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

(* This file is a wrapper around [elpi.apps.derive] that doesn't have the side
   effect of setting [Uniform Inductive Parameters]. *)

Require Export elpi.apps.derive.derive.
#[global] Unset Uniform Inductive Parameters.

(* Patch for the driver of the derive command. *)
Elpi Accumulate derive lp:{{/*(*/
  pred derive-original-gref i:gref, o:gref.
  derive-original-gref TyGR OrigGR :- OrigGR = TyGR.

  pred unfold-constants i:gref, i:string, i:bool, i:gref, o:derive.
  unfold-constants OrigGR Prefix HasSynterp GR D :-
    P = derive-original-gref GR OrigGR,
    derivation GR Prefix HasSynterp (derive Name Do Done),
    D = (derive Name (cl\ P => Do cl, !) (P => Done)).
  unfold-constants OrigGR Prefix HasSynterp (const C) D :-
    coq.env.const C (some (global C')) _,
    unfold-constants OrigGR Prefix HasSynterp C' D.

  pred constant-adapter-active.

  derivation (const C) Prefix HasSynterp D :-
    not(constant-adapter-active),
    coq.env.const C (some (global C')) _,
    constant-adapter-active =>
      unfold-constants (const C) Prefix HasSynterp C' D.
/*)*/}}.
