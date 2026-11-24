Require Import skylabs.prelude.prelude.
Require Import skylabs.lang.cpp.syntax.

Require test.test_cpp.

Definition stmts (s : Stmt) : list Stmt :=
  match s with
  | Sseq ss => ss
  | _ => [s]
  end.

(* The member initializers and the statements of a definition. *)
Definition definition (o : ObjValue) : option (list Initializer * list Stmt) :=
  match o with
  | Ofunction {| f_body := Some (Impl s) |} => Some ([], stmts s)
  | Omethod {| m_body := Some (UserDefined s | CompilerProvided s) |} =>
      Some ([], stmts s)
  | Oconstructor {| c_body := Some (UserDefined (inits, s) | CompilerProvided (inits, s)) |} =>
      Some (inits, stmts s)
  | _ => None
  end.

Definition global_function (n : name) : option ident :=
  match n with
  | Nglobal (Nfunction _ f _) => Some f
  | _ => None
  end.

(* The first [k] statements of the global functions [fns]. *)
Definition bodies (k : nat) (fns : list ident) (tu : translation_unit)
    : list (ident * list Stmt) :=
  omap (fun f =>
          head $ omap (fun '(n, o) =>
                         if bool_decide (global_function n = Some f)
                         then (fun d => (f, take k d.2)) <$> definition o
                         else None) (map_to_list tu.(symbols))) fns.

(* Typedefs and alias declarations. *)
Eval vm_compute in bodies 4
  [ "td_2d"; "td_ptr"; "td_ref"; "td_const_outer"; "td_array_of_ptr"
  ; "td_declarators"; "td_alias"; "td_paren"; "td_effect"; "td_sequenced"
  ; "td_init"; "td_of_td"; "td_fn_param"; "td_plain" ]%pstring test_cpp.source.
Eval vm_compute in bodies 4
  [ "td_typeof"; "td_typeof_expr"; "td_decltype"; "td_fn_ret"; "td_atomic"
  ; "td_memptr"; "td_tmp"; "td_triv"; "td_dflt"; "td_unsequenced" ]%pstring
  test_cpp.source.
