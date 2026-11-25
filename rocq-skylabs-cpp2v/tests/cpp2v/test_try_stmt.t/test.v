Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require test.test_cpp.

Definition function_body (n : name) : option Stmt :=
  match test_cpp.source.(symbols) !! n with
  | Some (Ofunction f) =>
      match f.(f_body) with Some (Impl s) => Some s | _ => None end
  | _ => None
  end.

Definition ctor_body (n : name) : option (list Initializer * Stmt) :=
  match test_cpp.source.(symbols) !! n with
  | Some (Oconstructor c) =>
      match c.(c_body) with Some (UserDefined b) => Some b | _ => None end
  | _ => None
  end.

(* A [try] function lowers to the body of its twin without [try]: the
   try-block is kept, and the handlers are dropped. [is_Some] rules out two
   missing symbols comparing equal. *)
Definition lowers_like (n_try n_ref : name) : Prop :=
  is_Some (function_body n_try) /\ function_body n_try = function_body n_ref.

#[local] Ltac check := split; [eexists; vm_compute; reflexivity | vm_compute; reflexivity].

Example catch_all : lowers_like "try_add_one(int)" "ref_add_one(int)".
Proof. check. Qed.

Example typed_handlers :
  lowers_like "try_typed_handlers(int)" "ref_typed_handlers(int)".
Proof. check. Qed.

Example nested : lowers_like "try_nested(int)" "ref_nested(int)".
Proof. check. Qed.

Example control_flow :
  lowers_like "try_control_flow(int)" "ref_control_flow(int)".
Proof. check. Qed.

Example throw_kept : lowers_like "try_throw(int)" "ref_throw(int)".
Proof. check. Qed.

Example function_block :
  lowers_like "try_function_block(int)" "ref_function_block(int)".
Proof. check. Qed.

Example ctor_function_block :
  is_Some (ctor_body "S::S(int)") /\
  ctor_body "S::S(int)" = ctor_body "S::S(int, long)".
Proof. check. Qed.
