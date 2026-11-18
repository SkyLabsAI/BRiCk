Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require alloca_cpp.

Definition compared_callee (n : name) : option Expr :=
  match alloca_cpp.source.(symbols) !! n with
  | Some (Ofunction f) =>
      match f.(f_body) with
      | Some (Impl (Sseq [Sreturn (Some
          (Ebinop Beq (Ecall callee [_; _]) _ _))])) => Some callee
      | _ => None
      end
  | _ => None
  end.

(* Stack allocation must retain its builtin semantics instead of calling an
   unrelated same-named function that returns null. *)
Example builtin_alloca_preserved :
  match compared_callee "builtin_call()"%cpp_name with
  | Some (Ecast (Cbuiltin2fun _) (Eglobal n _)) => Some n
  | _ => None
  end = Some (Nglobal (Nid "__builtin_alloca_with_align")).
Proof. vm_compute. reflexivity. Qed.

Example ordinary_alloca_preserved :
  match compared_callee "ordinary_call()"%cpp_name with
  | Some (Ecast Cfun2ptr (Eglobal n _)) => Some n
  | _ => None
  end = Some (Nglobal (Nid "alloca_with_align")).
Proof. vm_compute. reflexivity. Qed.
