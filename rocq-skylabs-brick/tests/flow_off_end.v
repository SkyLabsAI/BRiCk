(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import skylabs.iris.extra.bi.errors.
Require Import skylabs.lang.cpp.logic.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  Lemma Kreturn_nonvoid ty (Q : ptr -> mpred) :
    drop_qualifiers ty <> Tvoid -> Kreturn ty Q Normal |-- False.
  Proof.
    move=> H. rewrite /Kreturn /=.
    destruct (drop_qualifiers ty) eqn:E; cbn; try by rewrite ERROR_elim.
    by exfalso; apply H.
  Qed.

  Example Kreturn_int (Q : ptr -> mpred) : Kreturn "int" Q Normal |-- False.
  Proof. by rewrite /Kreturn /= ERROR_elim. Qed.
  Example Kreturn_class (Q : ptr -> mpred) : Kreturn "S" Q Normal |-- False.
  Proof. by rewrite /Kreturn /= ERROR_elim. Qed.
  Example Kreturn_void_normal (Q : ptr -> mpred) :
    Kreturn "void" Q Normal = (Forall p : ptr, p |-> primR "void" 1$m Vvoid -* Q p)%I.
  Proof. done. Qed.
  Example Kreturn_const_void_normal (Q : ptr -> mpred) :
    Kreturn "const void" Q Normal = (Forall p : ptr, p |-> primR "void" 1$c Vvoid -* Q p)%I.
  Proof. done. Qed.
End with_cpp.

Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.

cpp.prog implicit_main prog cpp:{{
int main() {}
namespace other { int main() {} }
}}.
cpp.prog explicit_main prog cpp:{{ int main() { return 7; } }}.

Definition function_body (tu : translation_unit) (n : name) : option FunctionBody :=
  match tu.(symbols) !! n with
  | Some (Ofunction f) => f.(f_body)
  | _ => None
  end.

Example main_implicit_return :
  function_body implicit_main "main()"%cpp_name =
    Some (Impl (Sseq [Sseq []; Sreturn_val (Eint 0 "int")])).
Proof. vm_compute. reflexivity. Qed.

Example other_main_has_no_implicit_return :
  function_body implicit_main "other::main()"%cpp_name = Some (Impl (Sseq [])).
Proof. vm_compute. reflexivity. Qed.

Example main_explicit_return :
  function_body explicit_main "main()"%cpp_name =
    Some (Impl (Sseq [Sreturn_val (Eint 7 "int")])).
Proof. vm_compute. reflexivity. Qed.
