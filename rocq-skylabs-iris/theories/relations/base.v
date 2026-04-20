Require Import iris.bi.bi.
Require Import iris.proofmode.tactics.

Module bi.
Section with_prop.
  Context {PROP : bi}.

  Definition bi_relation (T : Type) : Type := T -> T -> PROP.

  Declare Scope bi_relation_scope.
  Delimit Scope bi_relation_scope with bi_relation.
  Bind Scope bi_relation_scope with bi_relation.


  (* analog of [Basics.impl] *)
  Definition wand : bi_relation PROP := fun P Q => (P -∗ Q)%I.
  Definition flip {T} (r : bi_relation T) : bi_relation T := fun P Q => r Q P.

  Definition respectful {T U} (r1 : bi_relation T) (r2 : bi_relation U) : bi_relation (T -> U) :=
    λ P Q, (∀ x y, r1 x y -∗ r2 (P x) (Q y))%I.
  Notation "r1 ==> r2" := (respectful r1%bi_relation r2%bi_relation) (at level 55) : bi_relation_scope.

  Definition pointwise {T U} (r : bi_relation U) : bi_relation (T -> U) :=
    λ P Q, (∀ x : T, r (P x) (Q x))%I.
  Definition tpointwise {TT : tele} {U} (r : bi_relation U) : bi_relation (TT -t> U) :=
    λ P Q, (∀.. x : TT, r (tele_app P x) (tele_app Q x))%I.

  (* TODO: we should have <BiProperI> which does not include the <⊢> *)
  Definition BiProperI {T : Type} (rel : bi_relation T) (v : T) : PROP :=
    rel v v.
  Class BiProper {T : Type} (rel : bi_relation T) (v : T) : Prop :=
    _bi_proper : ⊢ BiProperI rel v.

  #[global]
  Instance forall_proper {T} : BiProper (pointwise wand ==> wand) (@bi_forall PROP T).
  Proof.
    red. iIntros (P Q) "X Y". iIntros (x). iApply "X". iStopProof. apply bi.forall_elim.
  Qed.
  #[global]
  Instance tforall_proper {T} : BiProper (pointwise wand ==> wand) (@bi_tforall PROP T).
  Proof.
    red. iIntros (P Q) "X Y". iIntros (x). iApply "X". iStopProof.
    rewrite bi_tforall_forall. apply bi.forall_elim.
  Qed.

  (* NOTE: this doesn't embody framing *)
  Lemma compose_bi_proper {T U V} (f : T -> U) (g : U -> V) (rT : bi_relation T) (rU : bi_relation U)
                          (rV : bi_relation V)
    : BiProper (respectful rT rU) f -> BiProper (respectful rU rV) g ->
      BiProper (respectful rT rV) (fun x => g (f x)).
  Proof.
    rewrite /BiProper/respectful; intros.
    iIntros (??) "A". iApply H0. iApply H. done.
  Qed.

  Lemma use_proper_1 {T : Type} {f : T -> PROP} (r1 : bi_relation T) (r2 : bi_relation PROP) (_ : BiProper (respectful r1 r2) f) :
    forall x y, ⊢ r1 x y -∗ r2 (f x) (f y).
  Proof.
    intros. iIntros "X". red in H. unfold respectful in H. iDestruct (H with "X") as "$".
  Qed.

  Require Import ExtLib.Data.HList.
  Fixpoint arrows (ts : list Type) (r : Type) : Type :=
    match ts with
    | nil => r
    | t :: ts => t -> arrows ts r
    end.

  Fixpoint applys (ts : list Type) (t : Type) : arrows ts t -> hlist (fun x => x) ts -> t :=
    match ts as ts return arrows ts t -> hlist _ ts -> t with
    | nil => fun f _ => f
    | x :: xs => fun f zs => applys _ _ (f (hlist_hd zs)) (hlist_tl zs)
    end.

  Fixpoint respectfuls {ts : list Type} {T : Type} (R : bi_relation T) :
    hlist bi_relation ts -> bi_relation (arrows ts T) :=
    match ts as ts return hlist _ ts -> bi_relation (arrows ts _) with
    | nil => fun _ => R
    | t :: ts => fun Rs => respectful (hlist_hd Rs) (respectfuls R $ hlist_tl Rs)
    end.

  Fixpoint pairs_foralls (Ts : list Type) : forall (K : hlist (fun x => x) Ts -> hlist (fun x => x) Ts -> Prop), Prop :=
    match Ts as Ts return (hlist _ Ts -> hlist _ Ts -> _) -> Prop with
    | nil => fun K => K Hnil Hnil
    | T :: Ts =>fun K => ∀ (x : T) (y : T), pairs_foralls Ts (fun xs ys => K (Hcons x xs) (Hcons y ys))
    end.

  (* TODO: this can be generalized *)
  Fixpoint args (ts : list Type) : hlist (fun x => x) ts -> hlist (fun x => x) ts -> hlist bi_relation ts -> PROP :=
    match ts as ts return hlist _ ts -> hlist _ ts -> hlist bi_relation ts -> PROP with
    | nil => fun _ _ _ => emp
    | t :: ts => fun xs ys rs => hlist_hd rs (hlist_hd xs) (hlist_hd ys) ∗ args ts (hlist_tl xs) (hlist_tl ys) (hlist_tl rs)
    end%I.

  Lemma use_proper_tele {Ts : list Type} {T} (R : bi_relation T) : forall (Rs : hlist bi_relation Ts)
    (f : arrows Ts T)
    (_ : BiProper (respectfuls R Rs) f),
    pairs_foralls Ts (λ xs ys, args _ xs ys Rs ⊢ R (applys _ _ f xs) (applys _ _ f ys)).
  Proof.
    induction Ts; simpl; intros.
    { apply H. }
    { admit. }
  Admitted.

End with_prop.
End bi.
