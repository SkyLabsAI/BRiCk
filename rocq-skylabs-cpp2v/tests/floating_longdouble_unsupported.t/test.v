Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require test.test_cpp.

Definition longdouble_return_expr : option Expr :=
  match test_cpp.module.(symbols) !! Nglobal (Nfunction function_qualifiers.N "longdouble_literal" []) with
  | Some (Ofunction f) =>
      match f.(f_body) with
      | Some (Impl (Sseq [Sreturn (Some e)])) => Some e
      | _ => None
      end
  | _ => None
  end.

Definition is_unsupported_expr (e : option Expr) : bool :=
  match e with
  | Some (Eunsupported _ (Tunsupported _)) => true
  | _ => false
  end.

Example longdouble_literal_is_explicitly_unsupported :
  is_unsupported_expr longdouble_return_expr = true :=
  ltac:(vm_compute; reflexivity).
