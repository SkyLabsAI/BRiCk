(*
 * Copyright (c) 2021 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export bluerock.prelude.telescopes.
Require Import iris.algebra.ofe.

(** Support for guarded recursive specs. *)
Section tele_fun_ofe.
  Context {t : tele} {SI : sidx} {A : ofe}.

  (** Imposing a discrete order here might be limiting in practice,
      but the same limitation exists upstream; for example, in
      [bi_texist_ne]. *)
  Instance tele_fun_equiv : Equiv (t -t> A) :=
    fun f g => forall x, tele_app f x ≡ tele_app g x.
  Instance tele_fun_dist : Dist (t -t> A) :=
    fun n f g => forall x, tele_app f x ≡{n}≡ tele_app g x.

  Lemma tele_fun_ofe_mixin : OfeMixin (t -t> A).
  Proof. exact: (iso_ofe_mixin (A:=tele_arg t -d> A) tele_app). Qed.

  Canonical Structure tele_funO := Ofe (t -t> A) tele_fun_ofe_mixin.
End tele_fun_ofe.
Arguments tele_funO {_} _ _ : assert.
