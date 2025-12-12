Require Import bluerock.lang.cpp.semantics.values.
Require Import bluerock.prelude.arith.builtins.

(* TODO: this file is misplaced *)

Section has_type_prop.
  Context {σ : genv}.

    Lemma has_type_prop_bswap8:
      forall v,
        has_type_prop (Vint (bswap8 v)) Tuchar.
    Proof. intros *; apply has_int_type; red; generalize (bswap8_bounded v); simpl; lia. Qed.

    Lemma has_type_prop_bswap16:
      forall v,
        has_type_prop (Vint (bswap16 v)) Tushort.
    Proof. intros *; apply has_int_type; red; generalize (bswap16_bounded v); simpl; lia. Qed.

    Lemma has_type_prop_bswap32:
      forall v,
        has_type_prop (Vint (bswap32 v)) Tuint.
    Proof. intros *; apply has_int_type; red; generalize (bswap32_bounded v); simpl; lia. Qed.

    Lemma has_type_prop_bswap64_long :
      forall v,
        has_type_prop (Vint (bswap64 v)) Tulong.
    Proof. intros *; apply has_int_type; red; generalize (bswap64_bounded v); simpl; lia. Qed.

    Lemma has_type_prop_bswap64:
      forall v,
        has_type_prop (Vint (bswap64 v)) Tulonglong.
    Proof. intros *; apply has_int_type; red; generalize (bswap64_bounded v); simpl; lia. Qed.

    Lemma has_type_prop_bswap128:
      forall v,
        has_type_prop (Vint (bswap128 v)) Tuint128_t.
    Proof. intros *; apply has_int_type; red; generalize (bswap128_bounded v); simpl; lia. Qed.

    Lemma has_type_prop_bswap:
      forall sz v,
        has_type_prop (Vint (bswap (int_rank.bitsize sz) v)) (Tnum sz Unsigned).
    Proof.
      intros *; destruct sz;
        eauto using
          has_type_prop_bswap8,
        has_type_prop_bswap16,
        has_type_prop_bswap32,
        has_type_prop_bswap64_long,
        has_type_prop_bswap64,
        has_type_prop_bswap128.
    Qed.

End has_type_prop.

#[global] Hint Resolve has_type_prop_bswap : has_type_prop.
