(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.syntax.supported.
Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.

(** * Attributes on functions and methods ([f_attrs], [m_attrs])

cpp2v preserves every attribute except those on its no-op list; the others
are [attr.Other], named by clang's attribute kind, which [supported] reports. *)

cpp.prog source flags "-std=c++20 --target=x86_64-linux-gnu" prog cpp:{{
void plain() {}
[[nodiscard]] __attribute__((always_inline, cold, visibility("hidden"))) inline int noops() { return 0; }
__attribute__((section(".cpulocal"))) void in_section() {}
[[noreturn]] void nr();
__attribute__((weak)) void weak_fn() {}
void nn(int *p) __attribute__((nonnull(1)));
void two() __attribute__((cold, section(".text.two")));
struct S {
  void m() __attribute__((section(".text.m")));
  virtual void v();
  void v2() const;
};
struct D : S {
  void v() override final;
};
}}.

Definition attr_names_of (n : name) : option (list PrimString.string) :=
  let names := List.map (fun a => match a with attr.Other name _ => name end) in
  match source.(symbols) !! n with
  | Some (Ofunction f) => Some (names f.(f_attrs))
  | Some (Omethod m) => Some (names m.(m_attrs))
  | _ => None
  end.

(* No attribute, or only no-op ones: nothing is recorded. *)
Example no_attributes :
  attr_names_of <$> ["plain()"; "noops()"; "D::v()"]%cpp_name =
  replicate 3 (Some []).
Proof. vm_compute. reflexivity. Qed.

(* Everything else is preserved, under clang's attribute kind. *)
Example preserved :
  attr_names_of <$> ["in_section()"; "nr()"; "weak_fn()"; "nn(int*)"; "two()"; "S::m()"]%cpp_name =
  Some <$> [["Section"]; ["CXX11NoReturn"]; ["Weak"]; ["NonNull"];
            ["Section"]; ["Section"]]%pstring.
Proof. vm_compute. reflexivity. Qed.

(* The pretty-printed form keeps the arguments. *)
Eval vm_compute in
  match source.(symbols) !! "in_section()"%cpp_name with
  | Some (Ofunction f) => f.(f_attrs)
  | _ => []
  end.

(* [supported] reports each preserved attribute. *)
Example supported_reports :
  supported.walk.attr (attr.Other "Weak" "__attribute__((weak))") =
  [supported.walk.Gap supported.walk.Unsupported "unsupported attribute: Weak"].
Proof. reflexivity. Qed.
