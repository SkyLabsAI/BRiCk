(*
 * Copyright (C) 2026 SkyLabs AI, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.ltac2.extra.extra.

Import Ltac2 Builder Printf.

Open Scope list_scope.
Import Lists.List.ListNotations.

Ltac2 custom_list_builder (build_a : 'a Builder.t) (build_b : 'b Builder.t) : ('a * 'a * 'b) Builder.t :=
  fun () =>
  error_context! [fprintf "custom list builder"]
  Ap.apply '(fun a b c => ([a] ++ [b] ++ List.rev c)%list) []
     (Ap.arg_on (fun (a,_,_) => a) build_a)
     (Ap.arg_on (fun (_,b,_) => b) build_a)
     (Ap.arg_on (fun (_,_,c) => c) build_b)
     Ap.done.

Ltac2 faulty_list_builder (build_a : 'a Builder.t) (build_b : 'b Builder.t) : ('a * 'a * 'b) Builder.t :=
  fun () =>
  error_context! [fprintf "faulty list builder"]
  Ap.apply '(fun a b c => (a ++ [b] ++ List.rev c)%list) []
     (Ap.arg_on (fun (a,_,_) => a) build_a)
     (Ap.arg_on (fun (_,b,_) => b) build_a)
     (Ap.arg_on (fun (_,_,c) => c) build_b)
     Ap.done.
