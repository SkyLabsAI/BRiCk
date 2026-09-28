Require Import iris.bi.monpred.
Require Import iris.base_logic.lib.iprop.
Require Import skylabs.lang.cpp.semantics.genv.
Require Import skylabs.lang.cpp.algebra.cfrac.
Require Import skylabs.lang.cpp.model.simple_pred.
Require Import skylabs.iris.extra.proofmode.proofmode.
Set Default Proof Using "Type*".

Section concrete_model.
  Context {thread_info : biIndex} {Σ : gFunctors}
    {Hlogic : SimpleCPP.cpp_logic thread_info Σ}.
  #[local] Existing Instance Hlogic.
  Context {σ : genv}.

  (** These are alternative descriptions of one full share; they need not
      be disjoint and cannot be combined using separating agreement. *)
  Lemma full_share_agreement ty p v1 v2 :
    <absorb> (SimpleCPP.tptsto (σ:=σ) ty 1$m p v1) ∧
    <absorb> (SimpleCPP.tptsto (σ:=σ) ty 1$m p v2) ⊢ ⌜v1 = v2⌝.
  Proof. apply SimpleCPP.tptsto_agree_and. Qed.
End concrete_model.

Set Printing Fully Qualified.
Print Assumptions CFracAgreement.cfrac_own_and_agree.
Print Assumptions CFracAgreement.cfrac_mpred_own_and_agree.
Print Assumptions CFracAgreement.big_sepL_and_agree.
Print Assumptions SimpleCPP.tptsto_agree_and.
Print Assumptions SimpleCPP.tptsto_agree.
Print Assumptions full_share_agreement.
