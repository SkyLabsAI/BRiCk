(*
 * Copyright (c) 2020-21 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.prelude.telescopes.
Require Import bluerock.lang.cpp.semantics.values.
Require Import bluerock.lang.cpp.logic.pred.
Require Import bluerock.lang.cpp.specs.spec_notations.
Require Export bluerock.lang.cpp.specs.classy.

Require Import bluerock.lang.cpp.specs.wp_spec_compat.

Set Printing Universes.

#[global] Instance val_HasVoid : HasVoid val := { _void := Vvoid }.

#[deprecated(since="2022-02-13",note="use [WpSpec].")]
Notation WithPrePostG := WpSpec (only parsing).
Bind Scope pre_spec_scope with WpSpec.

Notation WpSpec_cpp_val := (WpSpec mpredI val val) (only parsing).
Notation WpSpec_cpp_ptr := (WpSpec mpredI ptr ptr) (only parsing).

#[deprecated(since="2022-02-13",note="use [WpSpec_cpp_ptr].")]
Notation WithPrePost PROP := (WpSpec PROP ptr ptr) (only parsing).

(* These two classes provide automatic coercions between [ptr] and [val] and [Z] and [val]
 *)
#[global] Instance val_ptr_WithArg {spec} (WA : WithArg spec val) : WithArg spec ptr :=
  {| classy.add_arg p := classy.add_arg (Vptr p)
   ; classy.add_args p := classy.add_args (List.map Vptr p) |}.
#[global] Instance val_Z_WithArg {spec} (WA : WithArg spec val) : WithArg spec Z :=
  {| classy.add_arg p := classy.add_arg (Vint p)
   ; classy.add_args p := classy.add_args (List.map Vint p) |}.

Notation "'\spec' X" := (\spec@{WpSpec mpredI _ _} X).
Notation "'\this' this X" := (fun this : ptr => X%pre_spec) (only parsing).

Export classy.
Export bluerock.lang.cpp.specs.wp_spec_compat.
