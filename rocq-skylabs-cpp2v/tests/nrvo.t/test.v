Require Import skylabs.prelude.prelude.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.syntax.supported.

Require test.test_cpp.

Eval vm_compute in supported.check.translation_unit test_cpp.source.

(* The variables returned with [Sreturn_nrvo], per function, for the
   functions that have any. *)
Fixpoint nrvo_returns (s : Stmt) : list localname :=
  match s with
  | Sseq ss => flat_map nrvo_returns ss
  | Sif _ _ _ thn els => nrvo_returns thn ++ nrvo_returns els
  | Sreturn_nrvo x _ => x :: nil
  | _ => nil
  end.

Definition nrvo_functions (tu : translation_unit) : list (name * list localname) :=
  filter (fun p => bool_decide (p.2 <> nil)) $
  omap (fun '(n, o) =>
          match o with
          | Ofunction {| f_body := Some (Impl body) |} => Some (n, nrvo_returns body)
          | _ => None
          end) (map_to_list tu.(symbols)).

Eval vm_compute in nrvo_functions test_cpp.source.

(* The copy or move expression of each [Sreturn_nrvo], for the functions
   that differ in the constructor of the returned class. *)
Fixpoint nrvo_exprs (s : Stmt) : list Expr :=
  match s with
  | Sseq ss => flat_map nrvo_exprs ss
  | Sif _ _ _ thn els => nrvo_exprs thn ++ nrvo_exprs els
  | Sreturn_nrvo _ e => e :: nil
  | _ => nil
  end.

Definition nrvo_function_exprs (fns : list name) (tu : translation_unit) : list (name * list Expr) :=
  omap (fun n =>
          match tu.(symbols) !! n with
          | Some (Ofunction {| f_body := Some (Impl body) |}) => Some (n, nrvo_exprs body)
          | _ => None
          end) fns.

Eval vm_compute in nrvo_function_exprs
  [ "make(int*)"; "const_local(int*)"; "const_rvalue_ref()"; "copy_only()";
    "defaulted_move()"; "trivial()"; "templ()" ]%cpp_name test_cpp.source.
