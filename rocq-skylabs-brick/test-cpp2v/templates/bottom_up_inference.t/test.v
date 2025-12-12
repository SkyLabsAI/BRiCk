(*
 * Copyright (c) 2023-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.prelude.base.
Require Import bluerock.lang.cpp.msyntax.
Require Import test_17_cpp_templates.

Variant Error :=
| ResolvedTypeError (_ : MExpr) (observed : Mtype) (expected : Mtype)
| UnexpectedlyResolvedTerm (_ : MExpr)
| UnexpectedStmt (_ : MStmt)
| UnexpectedDecl (_ : MObjValue)
| MissingTest (_ : Mtranslation_unit)
.

Record result := Result { count : N; errs : list Error }.

Definition rzero : result := Result 0 nil.
Definition radd (r1 r2 : result) : result := Result (count r1 + count r2) (errs r1 ++ errs r2).
Definition rfail (e : Error) : result := Result 0 [e].

Definition check_list {A} (f : A -> result) (xs : list A) : result :=
  foldl (fun acc x => radd acc $ f x) rzero xs.

#[local] Notation C_TO_VOID e := (Eexplicit_cast cast_style.c Tvoid (Ecast C2void e)).

Definition check_expr (e : MExpr) : result :=
  match e with
  (** `CHECK(e,t)` *)
  | Ecomma (C_TO_VOID e) (Esizeof (inl t) _) =>
    Result 1 $
    let obs := type_of e in
    let exp := t in
    if bool_decide (obs = exp) then [] else [ResolvedTypeError e obs exp]

  (** `SKIP(e)` *)
  | Ecomma (C_TO_VOID _) (Esizeof (inr _) _) => Result 1 []


  (** `UNRESOLVED_XXX(e)` *)
  | Ecomma (C_TO_VOID (Eunresolved_member _ _)) (Eint 0 Tint)
  | Ecomma (C_TO_VOID (Eunresolved_unop _ _)) (Eint 1 Tint)
  | Ecomma (C_TO_VOID (Eunresolved_binop _ _ _)) (Eint 2 Tint)
  | Ecomma (C_TO_VOID (Eunresolved_call _ _ | Eunresolved_member_call _ _ _ | Eunresolved_parenlist _ _)) (Eint 3 Tint)

(*  | Ecomma (Eexplicit_cast cast_style.c C2void (Eunresolved_new _ _ _ _) _) (Eint 4 Tint)
  | Ecomma (Eexplicit_cast cast_style.c C2void (Eunresolved_delete _ _ _) _) (Eint 5 Tint)
*)
    => Result 1 []

  | _ => rfail $ UnexpectedStmt (Sexpr e)
  end.

Fixpoint check_stmt (s : MStmt) : result :=
  match s with
  | Sseq stmts => check_list check_stmt stmts
  | Sdecl _ => rzero
  | Sexpr e => check_expr e
  | _ => rfail $ UnexpectedStmt s
  end.

Definition run_test (tu : Mtranslation_unit) : result :=
  match tu.(msymbols) !! Ninst (Nglobal (Nfunction function_qualifiers.N "test" [])) [Atype (Tparam "T")] with
  | Some template =>
    let d := template.(template_value) in
    match d with
    | Ofunction f =>
      match f.(f_body) with
      | Some (Impl s) => check_stmt s
      | _ => rfail $ UnexpectedDecl d
      end
    | _ => rfail $ UnexpectedDecl d
    end
  | None => rfail $ MissingTest tu
  end.

Example test : run_test templates = Result 49 [].
Proof. vm_compute. reflexivity. Qed.
