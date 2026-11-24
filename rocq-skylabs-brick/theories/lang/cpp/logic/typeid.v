(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(** * Semantics of <<typeid>> ([expr.typeid])

    <<typeid>> is an lvalue of type <<const std::type_info>>
    (<https://eel.is/c++draft/expr.typeid#1>). cpp2v prints its operand as
    [inl ty] when the result is fixed at compile time (a type, or an
    unevaluated expression), with [ty] canonical and free of references and
    top-level cv-qualifiers ([expr.typeid]/5-7), and as [inr e] for a glvalue
    [e] of polymorphic class type ([expr.typeid]/4), whose dynamic type is
    read from [derivationR] (see [with_mdc]).

    <<typeid>> of a null polymorphic glvalue throws <<std::bad_typeid>>
    ([expr.typeid]/3); that case has no rule, as no [derivationR] exists for
    it. Both rules are stuck on types outside [typeid_ok].

    [specs/type_info.v] specifies <<std::type_info::operator==>>.
 *)
Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.lang.cpp.logic.pred.
Require Import skylabs.lang.cpp.logic.heap_pred.
Require Import skylabs.lang.cpp.logic.wp.
Require Import skylabs.lang.cpp.logic.dispatch.

(** ** The types that [type_infoR] identifies

    [type_infoR] identifies types by syntactic equality on [type] (see the
    <<std::type_info::operator==>> spec in [specs/type_info.v]). That is
    sound only on C++ types that cpp2v prints in exactly one way (the
    canonical form, never a reference or top-level cv-qualified type), and
    that no other C++ type prints like, in any translation unit.

    [typeid_ok ty] is a conservative allowlist of such printed types: both
    <<typeid>> rules are stuck on other types. It accepts
    - builtin arithmetic, character, [bool], [void] and <<std::nullptr_t>>
      types;
    - classes and enumerations whose name is built only from identifiers
      ([Nid]) of namespaces and classes, possibly instantiating templates
      with arguments that are themselves accepted types, or integer
      constants of integral or accepted enumeration type;
    - pointers to accepted types, which may be <<const>> and/or
      <<volatile>> unless they are arrays;
    - arrays of accepted types (hence with unqualified elements).

    It rejects, among others, the following types, where printing is not
    injective or not canonical:
    - function types, anywhere: cpp2v drops exception specifications, and
      [function_type_] has no cv- or ref-qualifiers for member functions, so
      <<typeid(void( * )() noexcept)>> and <<typeid(void( * )())>> would print
      the same, as would the types of <<&S::g>> and <<&S::h>> for a
      <<const>> member function <<g>> and a non-<<const>> <<h>>;
    - member pointers;
    - names under an anonymous namespace ([Nanonymous]), which print alike
      in every translation unit; names of local classes, which are scoped by
      their function's name ([Nfunction]), that a <<static>> function in
      another translation unit may share; unnamed classes and enumerations
      ([Nanon], [Nfirst_decl], [Nfirst_child]); and other names such as
      [Ndependent] or [Nunsupported];
    - references and top-level cv-qualifiers ([expr.typeid]/6-7): cpp2v
      removes them, so a hand-built <<Etypeid (inl (Tqualified QC Tint))>>
      would compare unequal to <<typeid(int)>>;
    - dependent, unsupported, attributed, realigned and architecture-specific
      types, and any other type constructor. *)
Fixpoint typeid_ok (ty : type) : bool :=
  match ty with
  | Tnum _ _ | Tchar_ _ | Tbool | Tvoid | Tnullptr | Tfloat_ _ => true
  | Tnamed n | Tenum n => typeid_ok_name n
  | Tptr (Tqualified QM _) => false
  | Tptr (Tqualified _ (Tarray _ _)) => false
  | Tptr (Tqualified _ t) | Tptr t => typeid_ok t
  | Tarray t _ => typeid_ok t
  | _ => false
  end
with typeid_ok_name (n : name) : bool :=
  match n with
  | Nglobal (Nid _) => true
  | Nscoped n (Nid _) => typeid_ok_name n
  | Ninst n args => typeid_ok_name n && forallb typeid_ok_arg args
  | _ => false
  end
with typeid_ok_arg (a : temp_arg) : bool :=
  match a with
  | Atype t => typeid_ok t
  | Avalue (Eint _ (Tnum _ _ | Tchar_ _ | Tbool)) => true
  | Avalue (Eint _ (Tenum n)) => typeid_ok_name n
  | _ => false
  end.

Module Type Expr__typeid.

  (** [p |-> type_infoR ty]: [p] is a <<std::type_info>> object that
      represents the type [ty]. <<std::type_info>> objects have static storage
      duration and are never modified, hence [Persistent]. Several objects may
      represent the same type ([expr.typeid]/1 does not promise one object
      per type). *)
  Parameter type_infoR : forall `{Σ : cpp_logic} {σ : genv}, type -> Rep.

  Section with_resolve.
    Context `{Σ : cpp_logic} {resolve : genv}.

    #[global] Declare Instance type_infoR_persistent ty : Persistent (type_infoR ty).
    #[global] Declare Instance type_infoR_affine ty : Affine (type_infoR ty).

    Variables (tu : translation_unit) (ρ : region).

    #[local] Notation wp_lval := (wp_lval tu ρ).
    #[local] Notation wp_glval := (wp_glval tu ρ).

    (** A type, or an expression that is not evaluated ([expr.typeid]/5-7).
        The rule is stuck on types outside [typeid_ok]. *)
    Axiom wp_lval_typeid_type : forall ty t Q,
          (if typeid_ok ty
           then Forall p : ptr, p |-> type_infoR ty -* Q p FreeTemps.id
           else False)
      |-- wp_lval (Etypeid (inl ty) t) Q.

    (** A glvalue of polymorphic class type ([expr.typeid]/4): the type of the
        most-derived object, if it is in [typeid_ok] (for instance, not a
        local class). *)
    Axiom wp_lval_typeid_expr : forall e t Q,
      match drop_qualifiers (type_of e) with
      | Tnamed cls =>
          wp_glval e (fun p free =>
            with_mdc p cls (fun mdc =>
              match mdc with
              | most_derived :: _ =>
                  if typeid_ok (Tnamed most_derived)
                  then Forall ti : ptr, ti |-> type_infoR (Tnamed most_derived) -* Q ti free
                  else False
              | [] => False
              end))
      | _ => False
      end
      |-- wp_lval (Etypeid (inr e) t) Q.
  End with_resolve.
End Expr__typeid.

Declare Module E__typeid : Expr__typeid.

Export E__typeid.
