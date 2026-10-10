Require Import iris.bi.monpred.
Require Import iris.base_logic.lib.iprop.
Require Import skylabs.prelude.base.
Require Import skylabs.prelude.arith.z_to_bytes.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.genv.
Require Import skylabs.lang.cpp.semantics.types.
Require Import skylabs.lang.cpp.algebra.cfrac.
Require Import skylabs.lang.cpp.model.inductive_pointers.
Require Import skylabs.lang.cpp.model.simple_pred.
Require Import skylabs.iris.extra.proofmode.proofmode.
Import PTRS_IMPL VALUES_DEFS_IMPL SimpleCPP.
Set Default Proof Using "Type*".

Lemma character_encoding_bounds ct n :
  in_Z_to_bytes_bounds (char_type.bitsize ct) Unsigned (Z.of_N n) <->
  (0 <= n < 2 ^ char_type.bitsN ct)%N.
Proof. destruct ct; rewrite /in_Z_to_bytes_bounds /=; lia. Qed.

Section encoding.
  Context {σ : genv}.

  Lemma initialized_character_encoding ct n vs :
    pure_encodes (Tchar_ ct) (Vchar n) vs <->
    (0 <= n < 2 ^ char_type.bitsN ct)%N /\
    vs = Z_to_bytes (char_type.bitsize ct) Unsigned (Z.of_N n).
  Proof.
    change
      (in_Z_to_bytes_bounds (char_type.bitsize ct) Unsigned (Z.of_N n) /\
       vs = Z_to_bytes (char_type.bitsize ct) Unsigned (Z.of_N n) <->
       (0 <= n < 2 ^ char_type.bitsN ct)%N /\
       vs = Z_to_bytes (char_type.bitsize ct) Unsigned (Z.of_N n)).
    by rewrite character_encoding_bounds.
  Qed.

  Lemma indeterminate_character_encoding ct vs :
    pure_encodes (Tchar_ ct) Vundef vs <->
    vs = repeat Rundef (N.to_nat (char_type.bytesN ct)).
  Proof. by destruct ct. Qed.

  (** Every value admitted by the existing character typing contract encodes. *)
  Lemma character_encoding_total ct v :
    has_type_prop v (Tchar_ ct) \/ v = Vundef ->
    exists vs, pure_encodes (Tchar_ ct) v vs.
  Proof.
    intros [H| ->].
    - apply has_type_prop_char in H. destruct H as (n & -> & Hn).
      eexists. apply initialized_character_encoding. by split.
    - eexists. apply indeterminate_character_encoding. done.
  Qed.

  Lemma character_encoding_size ct v vs :
    pure_encodes (Tchar_ ct) v vs ->
    size_of σ (Tchar_ ct) = Some (N.of_nat (length vs)).
  Proof. move=> /length_encodes ->. by rewrite /= N2Nat.id. Qed.

  Lemma character_upper_bound_rejected ct vs :
    ~ pure_encodes (Tchar_ ct) (Vchar (2 ^ char_type.bitsN ct)) vs.
  Proof. rewrite initialized_character_encoding. lia. Qed.

  Lemma character_maximum_encodes ct :
    pure_encodes (Tchar_ ct) (Vchar (2 ^ char_type.bitsN ct - 1))
      (Z_to_bytes (char_type.bitsize ct) Unsigned
        (Z.of_N (2 ^ char_type.bitsN ct - 1))).
  Proof. apply initialized_character_encoding. split; last done. destruct ct; cbn; lia. Qed.

  Lemma character_rejects_integer ct n vs :
    ~ pure_encodes (Tchar_ ct) (Vint n) vs.
  Proof. rewrite /pure_encodes /=. by intros H. Qed.

  Lemma indeterminate_character_not_zero ct :
    ~ pure_encodes (Tchar_ ct) Vundef
      (Z_to_bytes (char_type.bitsize ct) Unsigned 0).
  Proof. exact: pure_encodes_undef_Z_to_bytes. Qed.

  Lemma character16_little_endian :
    genv_byte_order σ = Little ->
    pure_encodes "char16_t"%cpp_type (Vchar 258) [Rval 2%N; Rval 1%N].
  Proof.
    intros H. apply initialized_character_encoding. split; first by cbn; lia.
    rewrite /Z_to_bytes H z_to_bytes._Z_to_bytes_eq. by vm_compute.
  Qed.

  Lemma character16_big_endian :
    genv_byte_order σ = Big ->
    pure_encodes "char16_t"%cpp_type (Vchar 258) [Rval 1%N; Rval 2%N].
  Proof.
    intros H. apply initialized_character_encoding. split; first by cbn; lia.
    rewrite /Z_to_bytes H z_to_bytes._Z_to_bytes_eq. by vm_compute.
  Qed.
End encoding.

Section concrete_model.
  Context {thread_info : biIndex} {Σ : gFunctors}
    {Hlogic : SimpleCPP.cpp_logic thread_info Σ}.
  #[local] Existing Instance Hlogic.
  Context {σ : genv}.

  Lemma physical_character_cell ct n p q a :
    (0 <= n < 2 ^ char_type.bitsN ct)%N ->
    let vs := Z_to_bytes (char_type.bitsize ct) Unsigned (Z.of_N n) in
    type_ptr (Tchar_ ct) p ∗ mem_inj_own p (Some a) ∗
    bytes a vs q ∗ vbytes a vs q ⊢ tptsto (Tchar_ ct) q p (Vchar n).
  Proof.
    intros Hn vs. iIntros "(T & M & B & V)".
    iApply (tptsto_physical_intro (Tchar_ ct) q p (Vchar n) a vs);
      first by destruct ct.
    iFrame. iSplit.
    - iPureIntro. apply initialized_character_encoding. by split.
    - iLeft. rewrite /has_type /=. iSplit; iPureIntro; last done.
      by apply has_type_prop_char'.
  Qed.

  Lemma physical_indeterminate_character ct p q a :
    let vs := repeat Rundef (N.to_nat (char_type.bytesN ct)) in
    type_ptr (Tchar_ ct) p ∗ mem_inj_own p (Some a) ∗
    bytes a vs q ∗ vbytes a vs q ⊢ tptsto (Tchar_ ct) q p Vundef.
  Proof.
    intros vs. iIntros "(T & M & B & V)".
    iApply (tptsto_physical_intro (Tchar_ ct) q p Vundef a vs);
      first by destruct ct.
    iFrame. iSplit; last by iRight.
    iPureIntro. by apply indeterminate_character_encoding.
  Qed.
End concrete_model.
