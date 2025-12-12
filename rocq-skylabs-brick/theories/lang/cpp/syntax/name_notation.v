(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require bluerock.lang.cpp.syntax.core.
Require Export bluerock.lang.cpp.syntax.notations.
Require bluerock.lang.cpp.syntax.name_notation.parser.
Require bluerock.lang.cpp.syntax.name_notation.printer.

Bind Scope cpp_name_scope with core.name.

#[local]
Definition parse_name (s : PrimString.string) := parser.parse_name s.
#[local]
Definition print_name (bs : core.name) := printer.print_name bs.

(* Name Aliases *)
Bind Scope cpp_name_scope with core.globname.
Bind Scope cpp_name_scope with core.obj_name.

(* the parser for fields adds a sanity check that it starts with [Nscoped] *)
#[local]
Definition field_parser (ls : PrimString.string) : option core.field :=
  match parse_name ls with
  | Some (core.Nscoped _ _) as x => x
  | _ => None
  end.
#[local]
Definition field_printer (f : core.field) : option PrimString.string :=
  match f with
  | core.Nscoped _ _ => print_name f
  | _ => None
  end.
String Notation core.field field_parser field_printer : cpp_field_scope.
(* NOTE: this needs to be registered **after** the parser for fields *)
String Notation core.name parse_name print_name : cpp_name_scope.
(* Bind Scope cpp_field_scope with core.field. *)
(* ^^ Does not work, because core.field coincides with core.name. *)


Fail Check "foo"%cpp_field.
Succeed Example _0 : "foo"%cpp_name = "foo"%cpp_name := eq_refl.

(** String Notations for types *)
#[local]
Definition parse_type (s : PrimString.string) := parser.parse_type s.
#[local]
Definition print_type (bs : core.type) := printer.print_type bs.
String Notation core.type parse_type print_type : cpp_type_scope.
Bind Scope cpp_type_scope with core.type.
