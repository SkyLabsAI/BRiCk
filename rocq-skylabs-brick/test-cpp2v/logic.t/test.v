Require Import bluerock.lang.cpp.logic.

Section with_Σ.
  Context `{Σ : !cpp_logic thread_info _Σ}.
  Section bi_inference.
    Definition mpred_sep (P Q : mpred) := P ** Q.
    Definition rep_sep (P Q : Rep) := P ** Q.
  End bi_inference.
End with_Σ.

About mpred_sep.
About rep_sep.

(* Test suite *)
Module Type TEST_SUITE.
Section test_suite.
  Context {σ : genv} `{Σ : !cpp_logic thread_info _Σ} (R : Rep) (f g : field) (o : offset) (p : ptr) (v : val).

  #[local] Ltac syntactically_equal :=
    lazymatch goal with
    | _ : _ |- ?X = ?X => idtac
    end;
    reflexivity.

  Check _at.
  Check _at p R.
  Check _offsetR.
  Check _offsetR o R.

  Goal o ., f = o ,, _field f.
  Proof. Show. syntactically_equal. Qed.

  Goal p |-> R = _at p R.
  Proof. Show. syntactically_equal. Qed.

  Goal o |-> R = _offsetR o R.
  Proof. Show. syntactically_equal. Qed.

  (*Example _0 := |> p |-> R.

  Example _1 := |> p ., f |-> R.

  Example _1' := |> _eqv v ., f |-> R.*)

  Example _2 := p |-> _field f |-> R.
  Print _2.

  Example _3 := p .[ Tint ! 0 ] |-> R.
  Print _3.

  Example _4 := p |-> _field f .[ Tint ! 0 ] |-> R.
  Print _4.

  Example _4a := p ., f |-> R.
  Print _4a.

  Example _4b : p ., f .[ Tint ! 0] = (p ., f) .[ Tint ! 0].
  Proof. Show. syntactically_equal. Qed.

  Example _5 := p .[ Tint ! 0 ] .[ Tint ! 3 ] |-> R.
  Print _5.

  Example _6 := p ., f .[ Tint ! 0 ] ., g |-> R.
  Print _6.

  Example _7 := p ., g ., f .[ Tint ! 1 ] .[ Tint ! 0 ] ., f |-> _field f |-> R.
  Print _7.

  Example _8 := p ., g ., f .[ Tint ! 1 ] .[ Tint ! 0 ] ., f |-> .[ Tint ! 1 ] |-> R.
  Print _8.

  Example _9 := o ., g ., f .[ Tint ! 1 ] .[ Tint ! 0 ] ., f |-> R.
  Print _9.

  Example _11 := o .[ Tint ! 1 ] |-> R.
  Print _11.

  (*Example _13 := _eqv v .[ Tint ! 1 ] |-> R.

  Example _13' := _eqv v |-> R.*)

  Example _14 := .[ Tint ! 1 ] |-> R.
  Print _14.

  (*Example _15 := |> .[ Tint ! 1 ] |-> |> R.*)

  Example _16 := p .[ Tint ! 1] |-> _offsetR (_field f) R.
  Print _16.

  (*backwards compatibility*)
  Example b0 := _at p R.
  Print b0.

  Example b1 := _offsetR (_field f) R.
  Print b1.

  Example b2 := _at (p .[ Tint ! 1]) R.
  Print b2.

  Example b3 := _at (p .[ Tint ! 1]) (_offsetR (_field f) R).
  Print b3.

  (*failure cases*)
  (*Fail Example fail0 := p |-> ▷ R ∗ R.
  (*Fail Example fail1 := p |-> |> R ** R. (* requires parsing as [(p |-> |> R) ** R] *)*)

  Fail Example fail2 := p |-> R ** R.*) (* requires parsing as [(p |-> R) ** R] *)

  Fail Example fail3 := p |-> R q.
End test_suite.
End TEST_SUITE.
