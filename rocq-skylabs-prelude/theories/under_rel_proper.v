(*
 * Copyright (C) 2022 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.prelude.base.

Section under_proper.
  Context {T} {R : relation T} `{!RewriteRelation R} `{!Transitive R}.
  #[local] Set Default Proof Using "Type*".

  (** Support setoid rewriting under `Under_rel`.
  Upstream discussion at
  https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/.60Proper.20.2E.2E.2E.20.28Under_rel.20.2E.2E.2E.29.60

  These instances are written to be (almost) maximally general, but do not allow rewriting with a different relation [S] under [Under_rel T R], even when one can rewrite with [S] under [R].

  `RewriteRelation` is not necessary, but an attempt to limit backtracking in proof search.
  *)

  (* The second relation is [eq] because that position is where under places an
     existential variable and we don't need flexibility for rewriting that.
   *)
  #[export] Instance under_mono :
    Proper (flip R ==> eq ==> impl) (Under_rel T R).
  Proof. move=> b a /= + c _ <- +. rewrite Under_relE. apply: transitivity. Qed.
  #[export] Instance under_flip_mono :
    Proper (R ==> eq ==> flip impl) (Under_rel T R).
  Proof. move=> b a /= + c _ <- +. rewrite Under_relE. apply: transitivity. Qed.

  #[export] Instance under_proper `{!Symmetric R} :
    Proper (R ==> eq ==> iff) (Under_rel T R).
  Proof.
    move => b a /= E c _ <-.
    by split; rewrite E.
  Qed.
End under_proper.

#[export] Instance: Params (@Under_rel) 2 := {}.
