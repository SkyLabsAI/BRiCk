(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.lang.cpp.logic.wp.

(** * [FreeTemps.remove_var]

[Kfree] uses [FreeTemps.remove_var x free] when a function returns the local
[x] by named return value optimization ([ReturnNRVO x p]): [x] has become the
returned object, so its destruction must be skipped while every other
destruction in [free] still runs. *)

#[local] Open Scope free_scope.

Section remove_var.
  Variables (p q r : ptr).

  #[local] Notation x := "x"%pstring.
  #[local] Notation y := "y"%pstring.

  (** Destroying [x] becomes a no-op. *)
  Example remove_var_delete :
    FreeTemps.remove_var x (FreeTemps.delete (Some x) Tint p) = Some 1.
  Proof. reflexivity. Qed.

  (** [None] means [free] does not destroy [x]: the destruction of another
      variable, of a temporary (no name), of variadic arguments, or nothing at
      all. *)
  Example remove_var_other_var :
    FreeTemps.remove_var x (FreeTemps.delete (Some y) Tint p) = None.
  Proof. reflexivity. Qed.
  Example remove_var_temporary :
    FreeTemps.remove_var x (FreeTemps.delete None Tint p) = None.
  Proof. reflexivity. Qed.
  Example remove_var_va :
    FreeTemps.remove_var x (FreeTemps.delete_va [] p) = None.
  Proof. reflexivity. Qed.
  Example remove_var_id :
    FreeTemps.remove_var x 1 = None.
  Proof. reflexivity. Qed.

  (** The shape [wp_decl_var] produces for a block declaring only [x]. *)
  Example remove_var_decl :
    FreeTemps.remove_var x (1 >*> FreeTemps.delete (Some x) Tint p)
    = Some (1 >*> 1).
  Proof. reflexivity. Qed.

  (** Only the destruction of [x] goes; the order of the others is kept. *)
  Example remove_var_seq_right :
    FreeTemps.remove_var x
      (FreeTemps.delete (Some y) Tint q >*> FreeTemps.delete (Some x) Tint p)
    = Some (FreeTemps.delete (Some y) Tint q >*> 1).
  Proof. reflexivity. Qed.
  Example remove_var_seq_left :
    FreeTemps.remove_var x
      (FreeTemps.delete (Some x) Tint p >*> FreeTemps.delete None Tint r)
    = Some (1 >*> FreeTemps.delete None Tint r).
  Proof. reflexivity. Qed.
  Example remove_var_par :
    FreeTemps.remove_var x
      (FreeTemps.delete None Tint r |*| FreeTemps.delete (Some x) Tint p)
    = Some (FreeTemps.delete None Tint r |*| 1).
  Proof. reflexivity. Qed.

  (** A temporary at [x]'s address is not [x]: matching is by name only. *)
  Example remove_var_by_name :
    FreeTemps.remove_var x
      (FreeTemps.delete None Tint p >*> FreeTemps.delete (Some x) Tint p)
    = Some (FreeTemps.delete None Tint p >*> 1).
  Proof. reflexivity. Qed.

  (** With two destructions named [x] (an inner [x] shadowing an outer one),
      only the first, the innermost, is removed. *)
  Example remove_var_first_only :
    FreeTemps.remove_var x
      (FreeTemps.delete (Some x) Tint p >*> FreeTemps.delete (Some x) Tint q)
    = Some (1 >*> FreeTemps.delete (Some x) Tint q).
  Proof. reflexivity. Qed.
End remove_var.
