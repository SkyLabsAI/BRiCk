Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require freestanding_cpp.

Definition returned (n : name) : option Expr :=
  match freestanding_cpp.source.(symbols) !! n with
  | Some (Ofunction f) =>
      match f.(f_body) with
      | Some (Impl (Sseq [Sreturn (Some e)])) => Some e
      | _ => None
      end
  | _ => None
  end.

(* The builtin computes 3, as checked by the C++ static_assert. Its explicit
   builtin identity must survive even when implicit builtins are disabled. *)
Example builtin_abs_preserved :
  match returned "builtin_call()"%cpp_name with
  | Some (Ecall (Ecast (Cbuiltin2fun _) (Eglobal n _)) [_]) => Some n
  | _ => None
  end = Some (Nglobal (Nid "__builtin_abs")).
Proof. vm_compute. reflexivity. Qed.

Example ordinary_abs_preserved :
  match returned "ordinary_call()"%cpp_name with
  | Some (Ecall (Ecast Cfun2ptr (Eglobal n _)) [_]) => Some n
  | _ => None
  end = Some (Nglobal (Nid "abs")).
Proof. vm_compute. reflexivity. Qed.

Example ordinary_abs_returns_seven :
  returned (Nglobal (Nid "abs")) = Some (Eint 7 Tint).
Proof. vm_compute. reflexivity. Qed.
