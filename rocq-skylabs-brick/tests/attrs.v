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

cpp2v preserves every attribute as [attr.Other], named by clang's attribute
kind; [supported] reports those that are not on its no-op list. *)

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
typedef int over_aligned __attribute__((aligned(16)));
typedef int quiet __attribute__((unused));
over_aligned g_aligned;
quiet g_quiet;
}}.

Definition attrs_of (n : name) : option (list attr.t) :=
  match source.(symbols) !! n with
  | Some (Ofunction f) => Some f.(f_attrs)
  | Some (Omethod m) => Some m.(m_attrs)
  | _ => None
  end.

(* The attribute kinds that [supported] reports. *)
Definition reported (n : name) : option (list PrimString.string) :=
  (fun attrs : list attr.t => omap (fun a => match a with attr.Other kind _ =>
     if supported.walk.noop_attr kind then None else Some kind end) attrs)
  <$> attrs_of n.

(* Every attribute is recorded, including no-op ones... *)
Example recorded :
  List.map (fun n => option_map (@List.length attr.t) (attrs_of n)) ["plain()"; "noops()"; "D::v()"]%cpp_name =
  [Some 0; Some 4; Some 2].
Proof. vm_compute. reflexivity. Qed.

(* ... but [supported] accepts the no-op ones ([nodiscard], [always_inline],
   [cold], [visibility], [override], [final]). *)
Example noop_not_reported :
  reported <$> ["plain()"; "noops()"; "D::v()"]%cpp_name = replicate 3 (Some []).
Proof. vm_compute. reflexivity. Qed.

(* Everything else is reported, under clang's attribute kind. *)
Example reported_kinds :
  reported <$> ["in_section()"; "nr()"; "weak_fn()"; "nn(int*)"; "two()"; "S::m()"]%cpp_name =
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

(** ** Type attributes

A typedef's attributes are kept at each use of the typedef, as
[Tattributed]; the parser drops no-op ones ([attr.noop_kinds]). *)
Definition var_type (n : name) : option type :=
  match source.(symbols) !! n with
  | Some (Ovar t _) => Some t
  | _ => None
  end.

Example typedef_attributes :
  (fun ot => match ot with
          | Some (skylabs.lang.cpp.syntax.core.Tattributed [attr.Other k _] Tint) =>
              if PrimString.compare k "Aligned"%pstring is Eq then 1 else 0
          | Some Tint => 2
          | _ => 0
          end) <$> (var_type <$> ["g_aligned"; "g_quiet"]%cpp_name) = [1; 2].
Proof. vm_compute. reflexivity. Qed.
