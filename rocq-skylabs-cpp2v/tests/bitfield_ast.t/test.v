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
