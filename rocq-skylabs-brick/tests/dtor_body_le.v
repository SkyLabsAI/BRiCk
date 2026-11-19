(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.

(* A [Defaulted] destructor is [ObjValue_le] only a [Defaulted] one: cpp2v
   prints implicit and defaulted destructors as [Defaulted] even where clang
   defines them, so [Defaulted] need not refine any [CompilerProvided] body. *)

#[local] Definition dtor (body : option (OrDefault Stmt)) : ObjValue :=
  Odestructor
    {| d_class := "C"%cpp_name
     ; d_cc := CC_C
     ; d_exception := exception_spec.NoThrow
     ; d_body := body |}.

Example defaulted_le_defaulted :
  ObjValue_le (dtor (Some Defaulted)) (dtor (Some Defaulted)) = true.
Proof. vm_compute. reflexivity. Qed.

Example defaulted_not_le_empty :
  ObjValue_le (dtor (Some Defaulted)) (dtor (Some (CompilerProvided (Sseq [])))) = false.
Proof. vm_compute. reflexivity. Qed.

Example defaulted_not_le_nonempty :
  ObjValue_le (dtor (Some Defaulted)) (dtor (Some (CompilerProvided (Sseq [Sreturn None])))) = false.
Proof. vm_compute. reflexivity. Qed.

Example defaulted_not_le_user_defined :
  ObjValue_le (dtor (Some Defaulted)) (dtor (Some (UserDefined (Sseq [])))) = false.
Proof. vm_compute. reflexivity. Qed.

Example empty_not_le_defaulted :
  ObjValue_le (dtor (Some (CompilerProvided (Sseq [])))) (dtor (Some Defaulted)) = false.
Proof. vm_compute. reflexivity. Qed.
