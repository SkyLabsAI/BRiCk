(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export skylabs.prelude.base.

(* This is easier than using a telescope *)
Fixpoint list_implies (xs : list Prop) (P : Prop) : Prop :=
  match xs with
  | [] => P
  | x :: xs => x -> list_implies xs P
  end.

Lemma list_implies_iff xs P : list_implies xs P <-> (List.Forall (fun x => x) xs -> P).
Proof.
  elim: xs => [| x xs IH ] /=.
  - rewrite Forall_nil; tauto.
  - rewrite Forall_cons {}IH; tauto.
Qed.

Fixpoint list_and (xs : list Prop) : Prop :=
  match xs with
  | [] => True
  | [x] => x
  | x :: xs => x ∧ list_and xs
  end.

Lemma list_and_iff xs : list_and xs <-> List.Forall (fun x => x) xs.
Proof.
  case: xs => [|x xs] /=.
  { by rewrite Forall_nil. }
  elim: xs x => [|x' xs IH] x /=.
  - by rewrite Forall_singleton.
  - by rewrite Forall_cons IH.
Qed.
