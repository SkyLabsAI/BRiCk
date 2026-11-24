(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.

(** * Attributes that make a construct unsupported

BRiCk has no model for these attributes, and dropping them would give the
construct a different meaning, so cpp2v prints the construct as unsupported:

- a local variable with [__attribute__((cleanup(f)))], whose scope exit calls
  [f(&var)], is declared by an [Sunsupported] statement;
- a reference to a weak symbol that the translation unit does not define,
  which the linker may resolve to address 0, is [Eunsupported];
- a [[clang::trivial_abi]] class, whose by-value parameters the callee
  destroys, is [Dunsupported]. *)

cpp.prog source flags "-std=c++20 --target=x86_64-linux-gnu" prog cpp:{{
void set(int **pp) { **pp = 1; }

void cleanup() {
  int flag = 0;
  { int *p __attribute__((cleanup(set))) = &flag; }
  if (int *q __attribute__((cleanup(set))) = &flag) { }
  for (int *r __attribute__((cleanup(set))) = &flag; ; ) { break; }
  int *plain = &flag;
}

extern int weak_var __attribute__((weak));
extern int weak_def __attribute__((weak));
int weak_def = 3;
void hook() __attribute__((weak));
void hook_def() __attribute__((weak));
void hook_def() {}
struct C {
  static int s __attribute__((weak));
  void m() __attribute__((weak));
};
int strong;

void weak(C c) {
  (void)&weak_var;
  (void)&weak_def;
  if (hook) hook();
  hook_def();
  (void)&C::s;
  c.m();
  (void)&C::m;
  (void)&strong;
}

struct [[clang::trivial_abi]] T {
  bool *p;
  T(bool *q) : p(q) {}
  ~T();
};
struct U {
  bool *p;
  ~U();
};
}}.

Definition body_of (n : name) : option Stmt :=
  match source.(symbols) !! n with
  | Some (Ofunction f) =>
      match f.(f_body) with
      | Some (Impl s) => Some s
      | _ => None
      end
  | _ => None
  end.

(* The three declarations with [cleanup] are unsupported; [plain] is not. *)
Eval vm_compute in body_of "cleanup()".

(* The references to [weak_var], [hook], [C::s] and [C::m] are unsupported;
   those to the defined [weak_def] and [hook_def] and to [strong] are not. *)
Eval vm_compute in body_of "weak(C)".

(* [global_ptr_nonnull] applies only to symbols that the translation unit
   defines, so not to the undefined weak [weak_var] and [hook]. *)
Example defined_symbols :
  defines_symbol source <$> ["weak_var"; "hook()"; "weak_def"; "hook_def()"; "strong"]%cpp_name =
  [false; false; true; true; true].
Proof. vm_compute. reflexivity. Qed.

Example trivial_abi_unsupported :
  source.(types) !! "T"%cpp_name = Some (Gunsupported "trivial_abi classes are not supported").
Proof. vm_compute. reflexivity. Qed.

Example plain_struct_supported :
  if source.(types) !! "U"%cpp_name is Some (Gstruct _) then True else False.
Proof. vm_compute. exact I. Qed.
