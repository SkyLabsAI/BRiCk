(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import skylabs.lang.cpp.cpp.
Require Import skylabs.lang.cpp.logic.dispatch.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.

(** * Semantics of <<dynamic_cast>>

    [dyncast_in] on a small hierarchy, and the rules used by hand. *)

cpp.prog source prog cpp:{{
  struct A { virtual ~A() {} };
  struct B : A {};
  struct C : A {};
  struct X { virtual ~X() {} };
  struct D : B, C, X {};     // two [A] subobjects
  struct P : private X, B {};
  struct Q : protected B {};

  D* down(B* b) { return dynamic_cast<D*>(b); }
  const void* to_void(B* b) { return dynamic_cast<const void*>(b); }
}}.

Section dyncast.
  Context {σ : genv}.
  #[local] Notation dc mdc target := (dyncast_in source mdc%cpp_name target%cpp_name).

  (** Downcasts ([expr.dynamic.cast]/9.1). *)
  Example down_D : dc ["D"; "B"] "D" = Some (Some (base_to_derived "D" ["B"]%cpp_name)).
  Proof. by vm_compute. Qed.
  Example down_B : dc ["D"; "B"; "A"] "B" = Some (Some (base_to_derived "B" ["A"]%cpp_name)).
  Proof. by vm_compute. Qed.
  (** The static type itself. *)
  Example down_self : dc ["D"; "B"] "B" = Some (Some (base_to_derived "B" []%cpp_name)).
  Proof. by vm_compute. Qed.

  (** Crosscasts ([expr.dynamic.cast]/9.2). *)
  Example cross_X : dc ["D"; "B"] "X" =
    Some (Some (base_to_derived "D" ["B"]%cpp_name ,, derived_to_base "D" ["X"]%cpp_name)).
  Proof. by vm_compute. Qed.
  Example cross_C : dc ["D"; "X"] "C" =
    Some (Some (base_to_derived "D" ["X"]%cpp_name ,, derived_to_base "D" ["C"]%cpp_name)).
  Proof. by vm_compute. Qed.

  (** Ambiguous base: [D] has two [A] subobjects. *)
  Example ambiguous : dc ["D"; "X"] "A" = Some None.
  Proof. by vm_compute. Qed.

  (** Non-public bases. *)
  Example private_target : dc ["P"; "B"] "X" = Some None.
  Proof. by vm_compute. Qed.
  Example private_operand : dc ["P"; "X"] "B" = Some None.
  Proof. by vm_compute. Qed.
  Example protected_down : dc ["Q"; "B"] "Q" = Some None.
  Proof. by vm_compute. Qed.

  (** No object, or unknown classes. *)
  Example no_mdc : dc [] "D" = None.
  Proof. by vm_compute. Qed.
  Example unknown : dc ["Z"; "B"] "D" = None.
  Proof. by vm_compute. Qed.
End dyncast.

(** ** The rules, by hand *)
Section rules.
  Context `{Σ : cpp_logic} {σ : genv} (MOD : source ⊧ σ).
  Context (tu : translation_unit) (ρ : region).
  #[local] Set Default Proof Using "MOD".

  Lemma dyncast_down_D : dyncast ["D"; "B"]%cpp_name "D"%cpp_name =
    Some (Some (base_to_derived "D" ["B"]%cpp_name)).
  Proof. apply: (tu_dyncast_ok source MOD). by vm_compute. Qed.

  (** <<dynamic_cast<D*>(b)>> for a [b] of the [B] subobject of a [D]. *)
  Lemma wp_dynamic_cast_down e (p : ptr) q Q :
    type_of e = Tptr (Tnamed "B") -> p <> nullptr ->
    wp_operand tu ρ e (fun v free =>
      [| v = Vptr p |] ** p |-> derivationR "B" ["D"; "B"]%cpp_name q **
      (p |-> derivationR "B" ["D"; "B"]%cpp_name q -*
       Q (Vptr (p ,, base_to_derived "D" ["B"]%cpp_name)) free))
    |-- wp_operand tu ρ (Ecast (Cdynamic (Tptr (Tnamed "D"))) e) Q.
  Proof.
    move=> He Hp. rewrite -wp_operand_cast_dynamic_ptr He /=.
    iIntros "wp". iApply (wp_operand_wand with "wp").
    iIntros (v free) "(-> & D & HQ)". iExists p. iSplit; first done.
    rewrite bool_decide_false //. iExists ["D"; "B"]%cpp_name. iSplit.
    - iExists q. iFrame "D". by iSplit.
    - rewrite dyncast_down_D. by iApply "HQ".
  Qed.

  (** <<dynamic_cast<const void*>(b)>>: the most-derived object. *)
  Lemma wp_dynamic_cast_void e (p : ptr) q Q :
    type_of e = Tptr (Tnamed "B") -> p <> nullptr ->
    wp_operand tu ρ e (fun v free =>
      [| v = Vptr p |] ** p |-> derivationR "B" ["D"; "B"]%cpp_name q **
      (p |-> derivationR "B" ["D"; "B"]%cpp_name q -*
       Q (Vptr (p ,, base_to_derived "D" ["B"]%cpp_name)) free))
    |-- wp_operand tu ρ (Ecast (Cdynamic (Tptr (Tconst Tvoid))) e) Q.
  Proof.
    move=> He Hp. rewrite -wp_operand_cast_dynamic_void He /=.
    iIntros "wp". iApply (wp_operand_wand with "wp").
    iIntros (v free) "(-> & D & HQ)". iExists p. iSplit; first done.
    rewrite bool_decide_false //. iExists ["D"; "B"]%cpp_name. iSplit.
    - iExists q. iFrame "D". by iSplit.
    - by iApply "HQ".
  Qed.

  (** A null operand gives null. *)
  Lemma wp_dynamic_cast_null e Q :
    type_of e = Tptr (Tnamed "B") ->
    wp_operand tu ρ e (fun v free => [| v = Vptr nullptr |] ** Q (Vptr nullptr) free)
    |-- wp_operand tu ρ (Ecast (Cdynamic (Tptr (Tnamed "D"))) e) Q.
  Proof.
    move=> He. rewrite -wp_operand_cast_dynamic_ptr He /=.
    iIntros "wp". iApply (wp_operand_wand with "wp").
    iIntros (v free) "(-> & HQ)". iExists nullptr. iSplit; first done.
    by rewrite bool_decide_true.
  Qed.
End rules.
