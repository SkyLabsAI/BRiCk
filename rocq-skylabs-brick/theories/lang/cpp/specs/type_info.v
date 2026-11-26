(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(** * A specification of <<std::type_info::operator==>>

    An assumed specification of the library function, for clients to link
    (for instance <<cpp.spec "std::type_info::operator==(const std::type_info&) const"
    with (\this this \exact type_info_eq_wpp this)>> with auto). It is not an
    axiom: a client that uses it assumes it of its library.

    <<bool operator==(const type_info& rhs) const noexcept;>> returns whether
    both objects represent the same type
    (<https://eel.is/c++draft/type.info#2>). Comparing [type]s is sound
    because the <<typeid>> rules only give [type_infoR ty] for [ty] in
    [typeid_ok], where cpp2v prints each C++ type in one way and distinct
    C++ types differently (see ../logic/typeid.v).

    C++20 rewrites <<a != b>> to <<!(a == b)>>; the C++17 member
    <<operator!=>> has the dual specification.
 *)
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.lang.cpp.logic.
Require Import skylabs.lang.cpp.specs.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  Definition type_info_eq_wpp (this : ptr) : WpSpec_cpp_val :=
    \arg{rhs} "" (Vref rhs)
    \prepost{t1} this |-> type_infoR t1
    \prepost{t2} rhs |-> type_infoR t2
    \post[Vbool (bool_decide (t1 = t2))] emp.

  Definition type_info_eq_spec : function_spec :=
    SMethod "std::type_info" QC Tbool ["const std::type_info&"%cpp_type] (fun this =>
      cpp_spec Tbool ["const std::type_info&"%cpp_type] (type_info_eq_wpp this)).

  (** <<bool operator!=(const type_info& rhs) const noexcept;>> (C++17) *)
  Definition type_info_neq_wpp (this : ptr) : WpSpec_cpp_val :=
    \arg{rhs} "" (Vref rhs)
    \prepost{t1} this |-> type_infoR t1
    \prepost{t2} rhs |-> type_infoR t2
    \post[Vbool (bool_decide (t1 <> t2))] emp.

  Definition type_info_neq_spec : function_spec :=
    SMethod "std::type_info" QC Tbool ["const std::type_info&"%cpp_type] (fun this =>
      cpp_spec Tbool ["const std::type_info&"%cpp_type] (type_info_neq_wpp this)).
End with_cpp.
