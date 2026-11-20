Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.syntax.supported.

Require test.test_cpp.
Require test.base_cpp.

(** The supported bit-fields of each record, with their run. *)
Definition bitfields_of (n : globname) : option (list (ident * BitfieldInfo)) :=
  match types test_cpp.source !! n with
  | Some (Gopaque o) => Some o.(o_bitfields)
  | _ => None
  end.

Eval vm_compute in bitfields_of "S".
Eval vm_compute in bitfields_of "Bad".
Eval vm_compute in bitfields_of "Kinds".
Eval vm_compute in
  match types base_cpp.source !! "D"%cpp_name with
  | Some (Gopaque o) => Some o.(o_bitfields)
  | _ => None
  end.
Eval vm_compute in bitfields_of "U".

(** The body of a function. *)
Definition body_of (n : obj_name) : option Stmt :=
  match symbols test_cpp.source !! n with
  | Some (Ofunction f) =>
      match f.(f_body) with
      | Some (Impl s) => Some s
      | _ => None
      end
  | _ => None
  end.

Eval vm_compute in body_of "rd(const S&)".
Eval vm_compute in body_of "rd_arrow(const S*)".
Eval vm_compute in body_of "wr(S&, int)".
Eval vm_compute in body_of "compound(S&)".
Eval vm_compute in body_of "pre_inc(S&)".
Eval vm_compute in body_of "post_inc(S&)".
Eval vm_compute in body_of "comma_wr(S&, int)".
Eval vm_compute in body_of "assign_assign(S&)".
Eval vm_compute in body_of "cond_rd(S&, int&, bool)".
Eval vm_compute in body_of "cond_wr(S&, int&, bool)".
Eval vm_compute in body_of "discard(S&)".
Eval vm_compute in body_of "rd_bad(Bad&)".
Eval vm_compute in body_of "rd_union(U&)".

(** Every bit-field access is partially supported; nothing is unsupported. *)
Eval vm_compute in supported.check.translation_unit test_cpp.source.

(** * Separate nodes for bit-field glvalues

    Written before the implementation. Each bit-field glvalue is one of
    [Ebitfield], [Ebf_comma], [Ebf_if], [Ebf_assign], [Ebf_assign_op],
    [Ebf_preinc], [Ebf_predec], or, as an arm of [Ebf_if] only,
    [Ebf_glvalue e] for an ordinary glvalue [e]. Their consumers are
    [Cl2r_bitfield], [Ebf_postinc] and [Ebf_postdec], and the standard nodes
    that discard a value. Nothing else changes. *)
Section expected.
  #[local] Open Scope cpp_type_scope.
  #[local] Open Scope pstring_scope.

  #[local] Abbreviation s_a := (Ebitfield false (Evar "s" "S&") "a" "int").
  #[local] Abbreviation s_b := (Ebitfield false (Evar "s" "S&") "b" "int").
  #[local] Abbreviation x := (Evar "x" "int&").
  #[local] Abbreviation y := (Evar "y" "int&").
  #[local] Abbreviation rd e := (Ecast Cl2r e).
  #[local] Abbreviation i n := (Eint n "int").
  #[local] Abbreviation is_body f s := (body_of f = Some (Sseq s)) (only parsing).

  Goal is_body "rd(const S&)"
    [Sreturn (Some (Ecast Cl2r_bitfield (Ebitfield false (Evar "s" "const S&") "a" "int")))].
  Proof. vm_compute. reflexivity. Qed.

  Goal is_body "wr(S&, int)"
    [Sexpr (Ebf_assign s_a (rd (Evar "v" "int")) "int")].
  Proof. vm_compute. reflexivity. Qed.

  Goal is_body "compound(S&)"
    [Sexpr (Ebf_assign_op Badd s_b (i 3) "int")].
  Proof. vm_compute. reflexivity. Qed.

  Goal is_body "pre_inc(S&)"
    [Sreturn (Some (Ecast Cl2r_bitfield (Ebf_preinc s_a "int")))].
  Proof. vm_compute. reflexivity. Qed.

  Goal is_body "post_inc(S&)"
    [Sreturn (Some (Ebf_postinc s_a "int"))].
  Proof. vm_compute. reflexivity. Qed.

  Goal is_body "comma_wr(S&, int)"
    [Sexpr (Ebf_assign (Ebf_comma (Evar "x" "int") s_a) (i 1) "int")].
  Proof. vm_compute. reflexivity. Qed.

  Goal is_body "assign_assign(S&)"
    [Sexpr (Ebf_assign (Ebf_assign s_a (i 1) "int") (i 2) "int")].
  Proof. vm_compute. reflexivity. Qed.

  (** A mixed conditional: the ordinary arm is embedded explicitly. *)
  Goal is_body "cond_rd(S&, int&, bool)"
    [Sreturn (Some (Ecast Cl2r_bitfield
       (Ebf_if (rd (Evar "c" "bool")) s_a (Ebf_glvalue x) "int&")))].
  Proof. vm_compute. reflexivity. Qed.

  Goal is_body "cond_wr(S&, int&, bool)"
    [Sexpr (Ebf_assign
       (Ebf_if (rd (Evar "c" "bool")) s_a (Ebf_glvalue x) "int&") (i 9) "int")].
  Proof. vm_compute. reflexivity. Qed.

  (** A discarded bit-field glvalue needs no consumer node. *)
  Goal is_body "discard(S&)" [Sexpr s_a].
  Proof. vm_compute. reflexivity. Qed.

  Goal is_body "discard2(S&, int&)"
    [Sexpr (Ebf_assign s_a (i 1) "int"); Sexpr (Ebf_comma x s_b)].
  Proof. vm_compute. reflexivity. Qed.

  (** Nesting: comma inside a conditional inside a conditional. *)
  Goal is_body "nest_wr(S&, int&, int&, bool, bool)"
    [Sexpr (Ebf_assign
       (Ebf_if (rd (Evar "c1" "bool"))
          (Ebf_comma x s_a)
          (Ebf_if (rd (Evar "c2" "bool")) (Ebf_glvalue y) s_b "int&")
          "int&")
       (i 1) "int")].
  Proof. vm_compute. reflexivity. Qed.

  Goal is_body "nest_rd(S&, int&, bool)"
    [Sreturn (Some (Ecast Cl2r_bitfield
       (Ebf_comma x
          (Ebf_if (rd (Evar "c" "bool")) (Ebf_assign s_a (i 1) "int") (Ebf_glvalue x) "int&"))))].
  Proof. vm_compute. reflexivity. Qed.

  Goal is_body "nest_inc(S&, int&)"
    [Sexpr (Ebf_preinc
       (Ebf_comma x (Ebf_assign_op Badd (Ebf_preinc s_a "int") (i 1) "int")) "int")].
  Proof. vm_compute. reflexivity. Qed.

  Goal is_body "post_cond(S&, int&, bool)"
    [Sexpr (Ebf_postinc
       (Ebf_if (rd (Evar "c" "bool")) s_a (Ebf_glvalue x) "int&") "int")].
  Proof. vm_compute. reflexivity. Qed.

  Goal is_body "decs(S&)"
    [Sexpr (Ebf_predec s_a "int");
     Sexpr (Ebf_postdec s_b "int");
     Sreturn (Some (Ecast Cl2r_bitfield s_a))].
  Proof. vm_compute. reflexivity. Qed.

  (** Ordinary glvalues are untouched. *)
  Goal is_body "plain(int&, int&, bool)"
    [Sexpr (Eassign (Eif (rd (Evar "c" "bool")) x y "int&") (i 1) "int");
     Sexpr (Eassign (Ecomma x y) (i 2) "int");
     Sexpr (Epreinc (Eassign x (i 3) "int") "int");
     Sexpr (Epostinc y "int")].
  Proof. vm_compute. reflexivity. Qed.

  (** A bit-field that is only an operand does not make its parent one:
      [(s.a, x)] is an ordinary comma, and the conditional has prvalue arms. *)
  Goal is_body "operand_only(S&, int&, bool)"
    [Sreturn (Some (Ebinop Badd
       (rd (Ecomma s_a x))
       (Eif (rd (Evar "c" "bool"))
          (Ebinop Badd (Ecast Cl2r_bitfield s_a) (i 0) "int")
          (rd x) "int")
       "int"))].
  Proof. vm_compute. reflexivity. Qed.
End expected.
