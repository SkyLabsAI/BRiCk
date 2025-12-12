(*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export iris.proofmode.proofmode.

(* See https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/1041. *)
#[global] Remove Hints class_instances_frame.frame_bupd : typeclass_instances.
#[global] Remove Hints class_instances_frame.frame_fupd : typeclass_instances.
Section class_instances_frame.
  Context {PROP : bi}.
  Implicit Types P Q R : PROP.
  #[global] Instance frame_bupd `{!BiBUpd PROP} p R P Q :
    (FrameInstantiateExistDisabled → Frame p R P Q) →
    Frame p R (|==> P) (|==> Q) | 2.
  Proof. rewrite /Frame=>/(_ ltac:(constructor))<-. by rewrite bupd_frame_l. Qed.
  #[global] Instance frame_fupd `{!BiFUpd PROP} p E1 E2 R P Q :
    (FrameInstantiateExistDisabled → Frame p R P Q) →
    Frame p R (|={E1,E2}=> P) (|={E1,E2}=> Q) | 2.
  Proof. rewrite /Frame=>/(_ ltac:(constructor))<-. by rewrite fupd_frame_l. Qed.
End class_instances_frame.

(* https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/1042 *)
Import environments.
#[global]
Ltac iFrameAnyIntuitionistic ::=
  iStartProof;
  let rec go Hs :=
    match Hs with [] => idtac | ?H :: ?Hs => repeat iFrameHyp H; go Hs end in
  match goal with
  | |- envs_entails ?Δ _ =>
     let Hs := eval lazy in (env_dom (env_intuitionistic Δ)) in go Hs
  end.

#[global]
Ltac iFrameAnySpatial ::=
  iStartProof;
  let rec go Hs :=
    match Hs with [] => idtac | ?H :: ?Hs => try iFrameHyp H; go Hs end in
  match goal with
  | |- envs_entails ?Δ _ =>
     let Hs := eval lazy in (env_dom (env_spatial Δ)) in go Hs
  end.

(** Missing instances for [bi_intuitionistically_if], i.e. [□?b _]. *)
Section class_instances_intuitionistically_if.
  Context {PROP : bi}.
  Implicit Types P Q R : PROP.

  #[global] Instance persistent_intuitionistically_if b P:
    Persistent P -> Persistent (□?b P).
  Proof. case: b => //=. apply _. Qed.

  #[global] Instance affine_intuitionistically_if b P:
    Affine P -> Affine (□?b P).
  Proof. case: b => //=. apply _. Qed.

  (* TODO: not sure if this is useful *)
  (* #[global] Instance from_pure_intuitionistically_if_true b P (φ : Prop): *)
  (*   FromPure (negb b) P φ → FromPure true (□?b P) φ. *)
  (* Proof. case: b => //=. apply _. Qed. *)

  (* TODO: not sure if this is useful *)
  (* #[global] Instance into_persistent_intuitionistically_if_false b P Q: *)
  (*   IntoPersistent b P Q → IntoPersistent false (□?b P) Q. *)
  (* Proof. case: b => //=; apply _. Qed. *)

  #[global] Instance into_pure_intuitionistically_if b P φ :
    IntoPure P φ → IntoPure (□?b P) φ.
  Proof. destruct b => //=. apply _. Qed.

  #[global] Instance into_sep_intuitionistically_if `{BiPositive PROP} b P Q1 Q2:
    IntoSep P Q1 Q2 → IntoSep (□?b P) (□?b Q1) (□?b Q2).
  Proof. case: b => //=; apply _. Qed.

  #[global] Instance frame_intuitionistically_if_true b P Q R:
    Frame true P Q R->
    Frame true P (□?b Q) (□?b R) | 2.
  Proof.
    unfold Frame.
    destruct b; cbn in *; [|done].
    iIntros (H) "[##P #Q]". rewrite -H. by iFrame "#".
  Qed.

  #[global] Instance frame_intuitionistically_if p b P Q R:
    Frame p P Q R->
    Frame p (□?b P) (□?b Q) (□?b R) | 3.
  Proof.
    unfold Frame.
    destruct b, p; cbn in *.
    1: iIntros (H) "[##P #Q]".
    2: iIntros (H) "[#P #Q]".
    3: iIntros (H) "[#P Q]".
    4: iIntros (H) "[P Q]".
    all: rewrite -H; by iFrame "#∗".
  Qed.

  #[global] Instance frame_intuitionistically_intuitionistically_if p b P Q R:
    Frame p P Q R->
    Frame p (□ P) (□?b Q) (□?b R) | 2.
  Proof.
    unfold Frame.
    destruct b, p; cbn in *.
    1: iIntros (H) "[##P #Q]".
    2: iIntros (H) "[#P #Q]".
    3: iIntros (H) "[#P Q]".
    4: iIntros (H) "[P Q]".
    all: rewrite -H; by iFrame "#∗".
  Qed.
End class_instances_intuitionistically_if.
