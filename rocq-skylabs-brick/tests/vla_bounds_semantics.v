(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import skylabs.lang.cpp.logic.

(** * Declarations of variably modified types: [Dvla_bounds]

Derived consequences of [wp_decl] for [Dvla_bounds]: the bounds are
evaluated in order, each must be greater than zero, and the declaration
binds no name and creates no object. *)

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv} (tu : translation_unit).

  #[local] Open Scope Z_scope.

  (** Without bounds the declaration does nothing: the region is unchanged
      and nothing is left to destroy. *)
  Lemma wp_decl_vla_bounds_nil ρ (k : region -> FreeTemps -> epred) :
    wp_decl tu ρ (Dvla_bounds []) k = k ρ FreeTemps.id.
  Proof. done. Qed.

  (** The first bound is evaluated as an operand and its temporaries are
      destroyed; its value is an integer greater than zero. The other
      bounds follow, in the same region. *)
  Lemma wp_decl_vla_bounds_cons ρ e es (k : region -> FreeTemps -> epred) :
    wp_decl tu ρ (Dvla_bounds (e :: es)) k =
    wp_operand tu ρ e (fun v free =>
      interp tu free
        (Exists n : Z, [| v = Vint n |] ** [| 0 < n |] **
         wp_decl tu ρ (Dvla_bounds es) k)).
  Proof. done. Qed.

  (** A literal bound, as in <<typedef int A[3][n];>>: clang prints the
      constant bound of an array of variable-length arrays too. *)
  Lemma wp_decl_vla_bounds_int ρ n es (k : region -> FreeTemps -> epred) :
    has_type_prop (Vint n) Tint -> 0 < n ->
    wp_decl tu ρ (Dvla_bounds es) k
    |-- wp_decl tu ρ (Dvla_bounds (Eint n Tint :: es)) k.
  Proof.
    intros Hty Hn. rewrite wp_decl_vla_bounds_cons -wp_operand_int.
    iIntros "H". iSplit; first done.
    iApply interp_intro_id. iExists n. by iFrame "H".
  Qed.

  (** A bound that is not greater than zero has no behavior: the
      declaration yields any postcondition only from [False]. *)
  Lemma wp_decl_vla_bounds_positive ρ e es (k : region -> FreeTemps -> epred) :
    wp_decl tu ρ (Dvla_bounds (e :: es)) k
    |-- wp_operand tu ρ e (fun v free =>
          interp tu free (Exists n : Z, [| v = Vint n /\ 0 < n |] ** True)).
  Proof.
    rewrite wp_decl_vla_bounds_cons. iApply wp_operand_frame; first done.
    iIntros (v free). iApply interp_frame.
    iIntros "(%n & % & % & _)". iExists n. by iSplit.
  Qed.

  (** In a block, the declaration runs the rest of the block in the same
      region, and leaves nothing to destroy at the end of the scope. *)
  Lemma wp_block_vla_bounds ρ es ss Q :
    ▷ wp_vla_bounds tu ρ es (▷ wp_block tu ρ ss Q)
    |-- wp_block tu ρ (Sdecl [Dvla_bounds es] :: ss) Q.
  Proof.
    rewrite (wp_block_unfold _ ρ (Sdecl _ :: _)) /= /wp_block_head /= wp_decls_eq /=.
    iIntros "H !> !>". iApply (wp_vla_bounds_frame with "[] H").
    iIntros "H !> !> !> !>".
    iApply (wp_block_frame with "[] H"). iIntros (rt) "H".
    destruct rt; cbn; iApply interp_intro_seq; by do 2 iApply interp_intro_id.
  Qed.
End with_cpp.
