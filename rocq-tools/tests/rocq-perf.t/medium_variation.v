(* Generated file, do not edit. *)

Inductive N :=
  | O : N
  | S : N -> N.

(* Some comment. *)

Fixpoint add (n m : N) : N :=
  match n with
  | O => m
  | S n => S (add n m)
  end.

Lemma add_O_l (n : N) :  add O n = n.
Proof.
  reflexivity.
Qed.

Lemma add_S_l (n m : N) : add (S n) m = S (add n m).
Proof.
  reflexivity.
Qed.

Lemma add_O_r (n : N) : add n O = n.
Proof.
  induction n as [|n IH].
  - rewrite add_O_l. reflexivity.
  - rewrite add_S_l. rewrite IH. reflexivity.
Qed.

Lemma add_S_r (n m : N) : add n (S m) = S (add n m).
Proof.
  induction n as [|n IH].
  - rewrite add_O_l. rewrite add_O_l. reflexivity.
  - rewrite add_S_l. rewrite add_S_l. rewrite IH. reflexivity.
Qed.

Lemma add_comm (n m : N) : add n m = add m n.
Proof.
  induction n as [|n IH].
  - rewrite add_O_l. rewrite add_O_r. reflexivity.
  - rewrite add_S_l. rewrite add_S_r. rewrite IH. reflexivity.
Qed.

(* Some comment. *)
