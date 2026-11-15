Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require test.test_cpp.

Definition function_body (n : name) : option Stmt :=
  match test_cpp.source.(symbols) !! n with
  | Some (Ofunction f) =>
      match f.(f_body) with Some (Impl s) => Some s | _ => None end
  | _ => None
  end.

Fixpoint condition_declarations (s : Stmt) : list VarDecl :=
  match s with
  | Sseq ss => List.flat_map condition_declarations ss
  | Sfor _ decl _ _ body =>
      from_option (fun d => [d]) [] decl ++ condition_declarations body
  | Sif _ _ _ thn els => condition_declarations thn ++ condition_declarations els
  | _ => []
  end.

Definition declarations_in (n : name) : list VarDecl :=
  match function_body n with
  | Some s => condition_declarations s
  | None => []
  end.

(* Both source cases retain the actual zero initializer. The shadowing case
   must not accidentally read the outer variable initialized to one. *)
Example shadowed_binding_preserved :
  declarations_in "shadowed()"%cpp_name =
    [Dvar "value" "int"%cpp_type (Some (Eint 0 "int"%cpp_type))].
Proof. vm_compute. reflexivity. Qed.

Example unshadowed_binding_preserved :
  declarations_in "unshadowed()"%cpp_name =
    [Dvar "value" "int"%cpp_type (Some (Eint 0 "int"%cpp_type))].
Proof. vm_compute. reflexivity. Qed.

Example increment_can_use_condition_binding :
  match function_body "increment_binding()"%cpp_name with
  | Some (Sseq [Sdecl _; Sfor None (Some (Dvar nm _ (Some _))) (Some _) (Some _) (Sseq [Scontinue]); Sreturn _]) => Some nm
  | _ => None
  end = Some "step"%pstring.
Proof. vm_compute. reflexivity. Qed.

(* All seven declaration conditions survive, including the four class cases.
   Ordinary outer/inner loops have no condition declaration. *)
Example condition_declaration_counts :
  map (fun n => length (declarations_in n))
    ["shadowed()"%cpp_name; "unshadowed()"%cpp_name;
     "increment_binding()"%cpp_name; "ordinary()"%cpp_name;
     "normal_and_continue()"%cpp_name; "break_cleanup()"%cpp_name;
     "return_cleanup()"%cpp_name; "nested_continue()"%cpp_name] =
    [1; 1; 1; 0; 1; 1; 1; 1]%nat.
Proof. vm_compute. reflexivity. Qed.
