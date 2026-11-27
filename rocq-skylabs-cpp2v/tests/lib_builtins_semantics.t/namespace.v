Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require namespace_cpp.

Definition returned_callee (n : name) : option name :=
  match namespace_cpp.source.(symbols) !! n with
  | Some (Ofunction f) =>
      match f.(f_body) with
      | Some (Impl (Sseq [Sreturn (Some
          (Ecall (Ecast Cfun2ptr (Eglobal callee _)) [_]))])) => Some callee
      | _ => None
      end
  | _ => None
  end.

(* The existing C-linkage declaration is the library function even though it
   is nested in a namespace. Both calls must use that declaration's symbol. *)
Example builtin_strlen_reuses_namespace_declaration :
  returned_callee "builtin_call(const char*)"%cpp_name =
    Some (Nscoped (Nglobal (Nid "C")) (Nid "strlen")).
Proof. vm_compute. reflexivity. Qed.

Example ordinary_strlen_uses_namespace_declaration :
  returned_callee "ordinary_call(const char*)"%cpp_name =
    Some (Nscoped (Nglobal (Nid "C")) (Nid "strlen")).
Proof. vm_compute. reflexivity. Qed.

Example no_spurious_global_strlen :
  namespace_cpp.source.(symbols) !! Nglobal (Nid "strlen") = None.
Proof. vm_compute. reflexivity. Qed.
