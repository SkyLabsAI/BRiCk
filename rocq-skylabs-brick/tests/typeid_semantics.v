(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import skylabs.lang.cpp.cpp.
Require Import skylabs.lang.cpp.logic.dispatch.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.lang.cpp.specs.type_info.

(** * Semantics of <<typeid>>

    The rule for a polymorphic operand used by hand, the name of
    <<std::type_info::operator==>>, and the types that [typeid_ok] accepts.
    The <<std::type_info>> declaration stands in for <<typeinfo>>. *)

cpp.prog source prog cpp:{{
  namespace std {
    class type_info {
    public:
      virtual ~type_info();
      bool operator==(const type_info&) const noexcept;
    };
  }
  struct B { virtual ~B() {} };
  struct D : B {};

  bool same_type(B& x, B& y) { return typeid(x) == typeid(y); }
  bool static_type() { return typeid(int) == typeid(const int&); }
}}.

(** The name of <<operator==>> that [type_info_eq_spec] specifies. *)
Example type_info_eq_name :
  is_Some (source.(symbols) !! "std::type_info::operator==(const std::type_info&) const"%cpp_name).
Proof. vm_compute. by eexists. Qed.

Section rules.
  Context `{Σ : cpp_logic} {σ : genv} (tu : translation_unit) (ρ : region).

  (** <<typeid(x)>> for an lvalue [x] of the [B] subobject of a [D]. *)
  Lemma wp_typeid_dynamic e t (p : ptr) q Q :
    type_of e = Tnamed "B" -> valcat_of e = Lvalue ->
    wp_lval tu ρ e (fun p' free =>
      [| p' = p |] ** p |-> derivationR "B" ["D"; "B"]%cpp_name q **
      (p |-> derivationR "B" ["D"; "B"]%cpp_name q -*
       Forall ti : ptr, ti |-> type_infoR (Tnamed "D") -* Q ti free))
    |-- wp_lval tu ρ (Etypeid (inr e) t) Q.
  Proof.
    move=> He Hvc. rewrite -wp_lval_typeid_expr He /= /wp_glval Hvc.
    iIntros "wp". iApply (wp_lval_wand with "wp").
    iIntros (p' free) "(-> & D & HQ)". iExists ["D"; "B"]%cpp_name. iSplit.
    - iExists q. iFrame "D". by iSplit.
    - by iApply "HQ".
  Qed.
End rules.

(** ** [typeid_ok] on the types cpp2v prints *)
cpp.prog ops prog cpp:{{
  namespace std {
    class type_info {
    public:
      virtual ~type_info();
      bool operator==(const type_info&) const noexcept;
    };
  }
  struct B { virtual ~B() {} };
  enum class Col { red };
  enum Plain { p0 };
  namespace ns { struct In { struct Nested {}; }; }
  template<typename T, int N> struct Tm {};
  template<Col c> struct Tc {};
  struct S { void g() const; void h(); };
  namespace { struct Anon {}; }

  const std::type_info& ok_int() { return typeid(int); }
  const std::type_info& ok_void() { return typeid(void); }
  const std::type_info& ok_nullptr() { return typeid(decltype(nullptr)); }
  const std::type_info& ok_class() { return typeid(B); }
  const std::type_info& ok_enum() { return typeid(Col); }
  const std::type_info& ok_plain_enum() { return typeid(Plain); }
  const std::type_info& ok_nested() { return typeid(ns::In::Nested); }
  const std::type_info& ok_ptr() { return typeid(const volatile B* const); }
  const std::type_info& ok_ptr_ptr() { return typeid(const char* const*); }
  const std::type_info& ok_array() { return typeid(const int[2][3]); }
  const std::type_info& ok_inst() { return typeid(Tm<const int*, 3>); }
  const std::type_info& ok_inst_enum() { return typeid(Tc<Col::red>); }

  const std::type_info& ko_fun_ptr() { return typeid(void( * )()); }
  const std::type_info& ko_noexcept_fun_ptr() { return typeid(void( * )() noexcept); }
  const std::type_info& ko_const_method() { return typeid(&S::g); }
  const std::type_info& ko_method() { return typeid(&S::h); }
  const std::type_info& ko_inst_fun() { return typeid(Tm<void(), 0>); }
  const std::type_info& ko_anon() { return typeid(Anon); }
  const std::type_info& ko_local() { struct L {}; return typeid(L); }
}}.

(** The operand of the <<typeid>> that the function [n] returns. *)
Definition typeid_operand (tu : translation_unit) (n : name) : option type :=
  match tu.(symbols) !! n with
  | Some (Ofunction f) =>
      match f.(f_body) with
      | Some (Impl (Sseq ss)) =>
          match last ss with
          | Some (Sreturn (Some (Etypeid (inl ty) _))) => Some ty
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

Definition typeid_ok_of (tu : translation_unit) (n : name) : option bool :=
  typeid_ok <$> typeid_operand tu n.

Example typeid_ok_accepts :
  typeid_ok_of ops <$> ["ok_int()"; "ok_void()"; "ok_nullptr()"; "ok_class()";
    "ok_enum()"; "ok_plain_enum()"; "ok_nested()"; "ok_ptr()"; "ok_ptr_ptr()";
    "ok_array()"; "ok_inst()"; "ok_inst_enum()"]%cpp_name =
  replicate 12 (Some true).
Proof. vm_compute. reflexivity. Qed.

(** The types of the review counterexamples: function types (cpp2v drops
    <<noexcept>>, and <<&S::g>> and <<&S::h>> print the same type), names
    under an anonymous namespace, and local classes. *)
Example typeid_ok_rejects :
  typeid_ok_of ops <$> ["ko_fun_ptr()"; "ko_noexcept_fun_ptr()";
    "ko_const_method()"; "ko_method()"; "ko_inst_fun()"; "ko_anon()";
    "ko_local()"]%cpp_name =
  replicate 7 (Some false).
Proof. vm_compute. reflexivity. Qed.

(** The printed types of <<void( * )()>> and <<void( * )() noexcept>> are
    equal, as are those of <<&S::g>> and <<&S::h>>: [typeid_ok] must reject
    them. *)
Example typeid_noexcept_printed_alike :
  typeid_operand ops "ko_fun_ptr()" = typeid_operand ops "ko_noexcept_fun_ptr()".
Proof. vm_compute. reflexivity. Qed.
Example typeid_method_quals_printed_alike :
  typeid_operand ops "ko_const_method()" = typeid_operand ops "ko_method()".
Proof. vm_compute. reflexivity. Qed.

(** Types that cpp2v never prints as <<typeid>> operands: references and
    top-level cv-qualifiers (it removes them), and cv-qualified array
    elements and arrays under pointers (it puts cv on the elements). *)
Example typeid_ok_rejects_unprinted :
  typeid_ok <$> [Tqualified QC Tint; Tqualified QM Tint; Tref Tint; Trv_ref Tint;
    Tarray (Tqualified QC Tint) 2; Tptr (Tqualified QM Tint);
    Tptr (Tqualified QC (Tqualified QV Tint));
    Tptr (Tqualified QC (Tarray Tint 2))] =
  replicate 8 false.
Proof. vm_compute. reflexivity. Qed.
