(*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.semantics.
Require Import bluerock.lang.cpp.logic.pred.
Require Import bluerock.lang.cpp.logic.path_pred.
Require Import bluerock.lang.cpp.logic.heap_pred.
Require Import bluerock.lang.cpp.logic.wp.
Require Import bluerock.lang.cpp.logic.atomics.

Require Import bluerock.iris.extra.proofmode.proofmode.

Section cmpxchg_derived.
  Context `{Σ : cpp_logic} {resolve:genv}.
  Variables (M : coPset) (ρ : region).

  Local Notation wp_atom' := (wp_atom M) (only parsing).

  (* A successful SC compare and exchange n *)
  (* It succeeds because the location p has the expected value v, which is
    stored in expected_p. *)
  Lemma wp_atom_compare_exchange_n_cst_suc :
    forall p expected_p desired weak succmemord failmemord Q sz sgn v,
      let ty := Tnum sz sgn in
      [| weak = Vbool false |] **
      [| succmemord = _SEQ_CST |] ** [| failmemord = _SEQ_CST |] **
      (* local pre-cond *)
      |>  _eqv expected_p |-> primR ty 1$m (Vint v) **
      AU1 << (* atomic pre-cond: latest value of p is also v, because this is
                successful *)
              _eqv p |-> primR ty 1$m (Vint v) >> @M,∅
          << (* atomic post-cond: latest value is desired *)
              _eqv p |-> primR ty 1$m (Vint desired),
            COMM (_eqv expected_p |-> primR ty 1$m (Vint v) -* Q (Vbool true)) >>
      |-- wp_atom' "__atomic_compare_exchange_n" ty
                  (p::succmemord::expected_p::failmemord::Vint desired::weak::nil) Q.
  Proof.
    intros. iIntros "(F1 & F2 & F3 & Hex & AU)".
    iApply wp_atom_compare_exchange_n_cst. iFrame.
    iAuIntro1.
    iApply (aacc1_aupd_commit with "AU"); [done|].
    rewrite {1}/atomic1_acc.
    iIntros "Hp !>". iExists _. iFrame.
    iSplit. { by iIntros "$ !> $". }
    iIntros "!>" (b v') "[Hp F]".
    iDestruct "F" as %[(?&?&?)|(?&?&?)]; subst; [|done].
    iFrame. by eauto.
  Qed.

  (* A failed SC strong compare exchange, which tell us that the values are
    truly different. *)
  Lemma wp_atom_compare_exchange_n_cst_fail :
    forall p val_p desired weak succmemord failmemord Q sz sgn v expected_v,
      let ty := Tnum sz sgn in
      [| weak = Vbool false |] **
      [| succmemord = _SEQ_CST |] ** [| failmemord = _SEQ_CST |] **
      (* we know that the values are different *)
      [| v <> expected_v |] **
      |> _eqv val_p |-> primR ty 1$m (Vint expected_v) **
      AU1 << _eqv p |-> primR ty 1$m (Vint v) >> @M,∅
          << _eqv p |-> primR ty 1$m (Vint v),
            COMM (_eqv val_p |-> primR ty 1$m (Vint v) -* Q (Vbool false)) >>
      |-- wp_atom' "__atomic_compare_exchange_n" ty
                  (p::succmemord::val_p::failmemord::Vint desired::weak::nil) Q.
  Proof.
    intros. iIntros "(? & ? & ? & % & ? & AU)".
    iApply wp_atom_compare_exchange_n_cst. iFrame.
    iAuIntro1.
    iApply (aacc1_aupd_commit with "AU"); [done|].
    rewrite {1}/atomic1_acc.
    iIntros "? !>". iExists _. iFrame.
    iSplit. { by iIntros "$ !> $". }
    iIntros "!>" (b v') "[? F]".
    iDestruct "F" as %[(?&?&?)|(?&?&?)]; subst; [done|].
    iFrame. by eauto.
  Qed.

  (* An SC compare and exchange *)
  Lemma wp_atom_compare_exchange_cst_suc :
    forall q p expected_p desired_p weak succmemord failmemord Q
      sz sgn expected desired,
      let ty := Tnum sz sgn in
      [| weak = Vbool false |] **
      [| succmemord = _SEQ_CST |] ** [| failmemord = _SEQ_CST |] **
      |> ((* local pre-cond *)
          _eqv expected_p |-> primR ty 1$m (Vint expected) **
           _eqv desired_p |-> primR ty q (Vint desired)) **
      AU1 << _eqv p |-> primR ty 1$m (Vint expected) >> @M,∅
          << (* atomic post-cond: latest value is desired *)
              _eqv p |-> primR ty 1$m (Vint desired),
            COMM (_eqv expected_p |-> primR ty 1$m (Vint expected) **
                  _eqv desired_p |-> primR ty q (Vint desired) -* Q (Vbool true)) >>
      |-- wp_atom' "__atomic_compare_exchange" ty
                  (p::succmemord::expected_p::failmemord::desired_p::weak::nil) Q.
  Proof.
    intros. iIntros "(? & ? & ? & ? & AU)".
    iApply wp_atom_compare_exchange_cst. iFrame.
    iAuIntro1.
    iApply (aacc1_aupd_commit with "AU"); [done|].
    rewrite {1}/atomic1_acc.
    iIntros "? !>". iExists _. iFrame.
    iSplit. { by iIntros "$ !> $". }
    iIntros "!>" (b v') "[? F]".
    iDestruct "F" as %[(?&?&?)|(?&?&?)]; subst; [|done].
    iFrame. by eauto.
  Qed.

  Lemma wp_atom_compare_exchange_cst_fail :
    forall q p expected_p desired_p weak succmemord failmemord Q
      sz sgn v expected desired,
      let ty := Tnum sz sgn in
      [| weak = Vbool false |] **
      [| succmemord = _SEQ_CST |] ** [| failmemord = _SEQ_CST |] **
      (* we know that the values are different *)
      [| v <> expected |] **
      |> (_eqv expected_p |-> primR ty 1$m (Vint expected) **
           _eqv desired_p |-> primR ty q (Vint desired)) **
      AU1 << _eqv p |-> primR ty 1$m (Vint v) >> @M,∅
          << _eqv p |-> primR ty 1$m (Vint v),
            COMM (_eqv expected_p |-> primR ty 1$m (Vint v) **
                  _eqv desired_p |-> primR ty q (Vint desired) -* Q (Vbool false)) >>
      |-- wp_atom' "__atomic_compare_exchange" ty
                  (p::succmemord::expected_p::failmemord::desired_p::weak::nil) Q.
  Proof.
    intros. iIntros "(? & ? & ? & % & ? & AU)".
    iApply wp_atom_compare_exchange_cst. iFrame.
    iAuIntro1.
    iApply (aacc1_aupd_commit with "AU"); [done|].
    rewrite {1}/atomic1_acc.
    iIntros "? !>". iExists _. iFrame.
    iSplit. { by iIntros "$ !> $". }
    iIntros "!>" (b v') "[? F]".
    iDestruct "F" as %[(?&?&?)|(?&?&?)]; subst; [done|].
    iFrame. by eauto.
  Qed.
End cmpxchg_derived.
