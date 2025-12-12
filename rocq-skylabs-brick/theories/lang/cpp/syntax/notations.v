(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.lang.cpp.parser.notation.

(* This file simply sets up notation scopes, in particular,
   those that are needed by <<_names>> files.
 *)

Declare Scope cpp_type_scope.
Delimit Scope cpp_type_scope with cpp_type.

Declare Scope cpp_scope.
Delimit Scope cpp_scope with cpp.

Declare Scope cpp_field_scope.
Delimit Scope cpp_field_scope with cpp_field.

Declare Scope cpp_name_scope.
Delimit Scope cpp_name_scope with cpp_name.

(* (* XXX This is only parsing to work around Coq misusing it outside *)
(* [cpp_field_scope]. See #235. *) *)
(* Notation "` e `" := e (e custom cppglobal at level 200, at level 0, *)
(*                         only parsing) : cpp_field_scope. *)
(* Notation "` e `" := e (e custom cppglobal at level 200, at level 0, *)
(*                         only parsing) : cpp_name_scope. *)


(** Importing [cpp_notation] makes cpp2v-generated names generally
available as, e.g., [``::MyClass``]. *)
Module Export cpp_notation.
  Notation "'``' e '``'" := e
    (at level 0, e custom cppglobal at level 200,
      format "`` e ``") : cpp_scope.
  Open Scope cpp_scope.
End cpp_notation.
