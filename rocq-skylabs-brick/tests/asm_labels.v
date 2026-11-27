(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.lang.cpp.syntax.supported.

(** * Definitions of entities with an asm label are unsupported

BRiCk names an entity by its C++ name, while the linker binds the symbol that
its asm label names. Another object may define that symbol under another C++
name, and the linker may keep that definition, so cpp2v prints the definition
of a function, method or variable with an asm label as [Dunsupported]. A
declaration that is not a definition carries no code and stays supported. *)

cpp.prog source flags "-std=c++20 --target=x86_64-linux-gnu" prog cpp:{{
extern "C" int declared() __asm__("declared_sym");
extern "C" int defined() __asm__("defined_sym");
extern "C" __attribute__((weak)) int defined() { return 1; }
extern int var_decl __asm__("var_decl_sym");
int var_def __asm__("var_def_sym") = 1;
struct S {
  static void m() __asm__("m_sym");
  static void n() __asm__("n_sym");
};
void S::n() {}
int plain() { return declared(); }
}}.

Example labelled_symbols :
  List.map (fun n => bool_decide (is_Some (source.(symbols) !! n)))
    ["declared"; "defined"; "var_decl"; "var_def"; "S::m()"; "S::n()"; "plain()"]%cpp_name =
  [true; false; true; false; true; false; true].
Proof. vm_compute. reflexivity. Qed.

Eval vm_compute in supported.check.translation_unit source.
