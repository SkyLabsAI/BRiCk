(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.

(** * Syntax of <<dynamic_cast>> and <<typeid>>

    The AST cpp2v prints for <<dynamic_cast>> (to a pointer, a reference,
    <<void*>>, and an upcast), for <<typeid>> ([Etypeid]), and the
    [s_nonpublic_bases] of classes with non-public bases. The
    <<std::type_info>> declaration stands in for <<typeinfo>>. *)

cpp.prog source prog cpp:{{
  namespace std {
    class type_info {
    public:
      virtual ~type_info();
      bool operator==(const type_info&) const noexcept;
    };
  }
  struct B { virtual ~B() {} };
  struct D : B { int x = 0; };
  struct E { int y; };

  D* down(B* b) { return dynamic_cast<D*>(b); }
  D& down_ref(B& b) { return dynamic_cast<D&>(b); }
  void* to_void(B* b) { return dynamic_cast<void*>(b); }
  B* up(D* d) { return dynamic_cast<B*>(d); }

  typedef const int CI;
  const std::type_info& ti_int() { return typeid(int); }
  const std::type_info& ti_cref() { return typeid(const int&); }
  const std::type_info& ti_typedef() { return typeid(CI); }
  const std::type_info& ti_const_var(const int x) { return typeid(x); }
  const std::type_info& ti_nonpoly(const E& e) { return typeid(e); }
  const std::type_info& ti_poly_deref(B* b) { return typeid( *b ); }
  const std::type_info& ti_poly(B& x) { return typeid(x); }

  struct A1 {};
  struct A2 {};
  struct A3 {};
  struct P : private A1, protected A2, A3 {};
  class Q : A1, public A2 {};
}}.

Definition returned (tu : translation_unit) (n : name) : option Expr :=
  match tu.(symbols) !! n with
  | Some (Ofunction f) =>
      match f.(f_body) with
      | Some (Impl (Sseq [Sreturn (Some e)])) => Some e
      | _ => None
      end
  | _ => None
  end.

(** ** <<dynamic_cast>> *)
Eval vm_compute in returned source "down(B*)".
Eval vm_compute in returned source "down_ref(B&)".
Eval vm_compute in returned source "to_void(B*)".
Eval vm_compute in returned source "up(D*)".

(** ** <<typeid>> *)
Eval vm_compute in returned source "ti_int()".
Eval vm_compute in returned source "ti_cref()".
Eval vm_compute in returned source "ti_typedef()".
Eval vm_compute in returned source "ti_const_var(const int)".
Eval vm_compute in returned source "ti_nonpoly(const E&)".
Eval vm_compute in returned source "ti_poly_deref(B*)".
Eval vm_compute in returned source "ti_poly(B&)".

(** The type operands of <<typeid(int)>>, <<typeid(const int&)>>,
    <<typeid(CI)>> and of the unevaluated <<typeid(x)>> with <<x : const int>>
    print as the same type. *)
Example typeid_int_types_equal :
  returned source <$> ["ti_cref()"; "ti_typedef()"; "ti_const_var(const int)"]%cpp_name =
  [returned source "ti_int()"; returned source "ti_int()"; returned source "ti_int()"].
Proof. vm_compute. reflexivity. Qed.

(** ** Base access ([s_nonpublic_bases]) *)
Eval vm_compute in source.(types) !! "D"%cpp_name.
Eval vm_compute in source.(types) !! "P"%cpp_name.
Eval vm_compute in source.(types) !! "Q"%cpp_name.
