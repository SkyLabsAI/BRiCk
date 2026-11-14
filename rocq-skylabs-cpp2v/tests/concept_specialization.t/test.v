Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.syntax.supported.
Require test.test_cpp.

Definition body (nm : name) : option Stmt :=
  match test_cpp.source.(symbols) !! nm with
  | Some (Ofunction f) =>
      match f.(f_body) with
      | Some (Impl s) => Some s
      | _ => None
      end
  | _ => None
  end.

Definition return_expr (nm : name) : option Expr :=
  match body nm with
  | Some (Sseq [Sreturn (Some e)]) => Some e
  | _ => None
  end.

Definition condition (nm : name) : option Expr :=
  match body nm with
  | Some (Sseq [Sif _ _ e _ _]) => Some e
  | _ => None
  end.

Example resolved_true_value :
  return_expr "resolved_true()"%cpp_name = Some (Ebool true).
Proof. vm_compute. reflexivity. Qed.

Example resolved_false_value :
  return_expr "resolved_false()"%cpp_name = Some (Ebool false).
Proof. vm_compute. reflexivity. Qed.

Example instantiated_true_condition :
  condition "choice<int>()"%cpp_name = Some (Ebool true).
Proof. vm_compute. reflexivity. Qed.

Example instantiated_false_condition :
  condition "choice<char>()"%cpp_name = Some (Ebool false).
Proof. vm_compute. reflexivity. Qed.

Example instantiated_code_supported :
  supported.check.translation_unit test_cpp.static__source = [].
Proof. vm_compute. reflexivity. Qed.
