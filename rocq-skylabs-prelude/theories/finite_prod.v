(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.prelude.base.
Require Export bluerock.prelude.finite.
Require Import bluerock.prelude.option.

(**
Finite product of types coming from a function [A : name -> Type]
where [name] is finite.

- [to_list A] is the finite product type of the types in [A].

- [lookup (e : to_list A) (n : name) : A n] projects a value of type [A n]
  from the product value [e].
- [update (n : name) (v : A n) (e : to_list A) : to_list A] updates the
  part [n] of the product value [e] to [v].

- [fmap (k : ∀ (n : name), A n -> B n) (e : to_list A) : to_list B]
  applies the function [k] to all values in the product value [e].
- [fmapO (k : ∀ (n : name), A n -> option (B n)) (e : to_list A) : to_list B]
  traverses the product value [e] and applies the function [k] to all values,
  as long as [k] returns [Some _].

TODO: revise the API if/when we turn this into a proper framework.

TODO: overlaps with telescopes.
*)

Module fin_prod.

  Module internal.
    Definition to_list' {name : Type}
        (A : name -> Type) (names : list name) : Type :=
      foldr (λ n acc, (A n) * acc)%type ()%type names.

    Section with_fg.
      Context {name : Type}.
      Context {A B : name -> Type}.

      Fixpoint fmap' ns (k : ∀ (n : name), A n -> B n)
          : to_list' A ns -> to_list' B ns :=
        match ns with
        | [] => id
        | n' :: ns' => λ e, let '(fn',e') := e in (k n' fn', fmap' ns' k e')
        end.

      (**
      TODO: Consider splitting [fmapO'] into
      - @fmap' A (option ∘ B) and
      - traverse : to_list' (option ∘ B) -> option (to_list' B)
       *)
      Fixpoint fmapO' ns (k : ∀ (n : name), A n -> option (B n))
          : to_list' A ns -> option (to_list' B ns) :=
        match ns with
        | [] => λ _, Some () (** the inner most type is always () *)
        | n' :: ns' =>
            λ e, let '(fn',e') := e in
              kn ← k n' fn'; kns ← fmapO' ns' k e';
              Some (kn, kns)
        end.
    End with_fg.

    Section with_eq_dec.
      Context `{EqDecision name} {A : name -> Type}.

      Fixpoint lookup' ns : ∀ (e : to_list' A ns) (n : name), option (A n) :=
        match ns with
        | [] => λ _ _, None
        | n' :: ns' =>
          λ e n, let '(fn',e') := e in (* this destruct only works with [e] behind a λ *)
            if decide (n' = n) is left Heq
            then eq_rect n' (λ n1, option (A n1)) (Some fn') n Heq
            else lookup' ns' e' n
        end.

      Definition update' ns (n : name) (v : A n) : to_list' A ns -> to_list' A ns :=
        fmap' ns (λ n', if decide (n = n') is left Heq
                        then λ _ : A n', eq_rect n A v n' Heq
                        else id).
    End with_eq_dec.

    Section theory_with_type.
      Context {name : Type} {A : name -> Type}.

      Lemma to_list'_nil : to_list' A [] = ()%type.
      Proof. done. Qed.

      Lemma to_list'_cons n ns :
        to_list' A (n :: ns) = ((A n) * to_list' A ns)%type.
      Proof. by rewrite /to_list' foldr_cons. Qed.
    End theory_with_type.

    Section theory_with_eq_dec.
      Context `{EqDecision name} {A : name -> Type}.
      Context (ns : list name).
      Implicit Types (e : to_list' A ns) (n : name).

      Lemma lookup'_elem_of_Some e n :
        n ∈ ns -> is_Some (lookup' ns e n).
      Proof.
        induction ns as [|n' ns' IH].
        { by intros ?%not_elem_of_nil. }
        destruct e as [fn' e'].
        case (decide (n = n')) => ? Ins'.
        - subst n'.
          exists fn'. by rewrite /= decide_True_pi.
        - apply elem_of_cons in Ins' as [?|Ins']; [done|].
          apply (IH e') in Ins' as [fn Eqe].
          exists fn. rewrite /=. by case_match.
      Qed.

      Lemma lookup_update'_eq e n (v : A n) :
        n ∈ ns →
        lookup' ns (update' ns n v e) n = Some v.
      Proof.
        induction ns as [|n' ns' IH] => /= Inn.
        { by apply not_elem_of_nil in Inn. }
        destruct e as [fn e']. simpl.
        case (decide (n' = n)) => ? /=.
        { subst n'. by rewrite /= decide_True_pi. }
        apply IH. by apply elem_of_cons in Inn as [].
      Qed.

      Lemma lookup_update'_ne e n (v : A n) :
        ∀ n', n ≠ n' →
        lookup' ns (update' ns n v e) n' = lookup' ns e n'.
      Proof.
        induction ns as [|n' ns' IH] => /= nx NEq; [done|].
        destruct e as [fn e'].
        case (decide (n' = nx)) => ? /=.
        - subst n'. rewrite /=. by case_match.
        - by apply IH.
      Qed.

      Lemma lookup'_ext e1 e2 :
        NoDup ns →      (* to make sure a lookup result is unique *)
        (∀ n, n ∈ ns → lookup' ns e1 n = lookup' ns e2 n) → e1 = e2.
      Proof.
        induction ns as [|n' ns' IH] => ND EXT.
        { by destruct e1, e2. }
        destruct e1 as [fn1 e1'], e2 as [fn2 e2'].
        f_equal.
        - move : (EXT n') => /=.
          rewrite decide_True_pi /= => EQ.
          specialize (EQ ltac:(by left)). by inversion EQ.
        - apply NoDup_cons in ND as [NIn ND].
          apply (IH _ _ ND). intros n Inn'.
          move : (EXT n ltac:(by right)) => /=.
          case_match; [|done].
          subst. exfalso. by apply NIn.
      Qed.
    End theory_with_eq_dec.

    Section theory_with_fg.
      Context `{EqDecision name} {A B : name -> Type}.
      Context (ns : list name).

      Implicit Types (e : to_list' A ns) (n : name).

      Lemma lookup_fmap' (k : ∀ (n : name), A n -> B n) e n :
        lookup' ns (fmap' ns k e) n = (k n) <$> (lookup' ns e n).
      Proof.
        induction ns as [|n' ns' IH] => /=; [done|].
        destruct e as [fn e']. case_match; [by subst n'|].
        by apply IH.
      Qed.

      Lemma fmapO'_Some
          (k : ∀ (n : name), A n -> option (B n))
          (e : to_list' A ns) (e' : to_list' B ns) :
        NoDup ns →
        (∀ n, n ∈ ns → (k n) <$> (lookup' ns e n) = Some (lookup' ns e' n)) ↔
        fmapO' ns k e = Some e'.
      Proof.
        induction ns as [|n' ns' IH] => ND /=.
        { split.
          - simpl in e'. by destruct e'.
          - by intros _ ? ?%not_elem_of_nil. }
        destruct e as [fn e1].
        destruct e' as [fn' e1'].
        apply NoDup_cons in ND as [NIn ND].
        destruct (IH e1 e1' ND) as [IH1 IH2]. split.
        - intros IS. rewrite IH1.
          + specialize (IS n' ltac:(by left)).
            rewrite /= decide_True_pi /= in IS.
            inversion IS as [IS']. by rewrite IS' /=.
          + intros n Inn. move : (IS n ltac:(by right)).
            rewrite /=.
            case (decide (n' = n)) => NEq /=; [|done].
            subst n'. exfalso. by apply NIn.
        - intros (kn & Eqkn & (e'' & Eqe'' & EqS)%bind_Some)%bind_Some n Inn.
          inversion EqS. subst kn e''. clear EqS.
          apply elem_of_cons in Inn as [?|Ins'].
          + subst n'. by rewrite decide_True_pi /= Eqkn.
          + case (decide (n' = n)) => NEq /=.
            * subst n'. exfalso. by apply NIn.
            * by apply IH2.
      Qed.

      Lemma fmapO'_Some_1
          (k : ∀ (n : name), A n -> option (B n))
          (e : to_list' A ns) (e' : to_list' B ns) :
        NoDup ns →
        (∀ n, n ∈ ns → (k n) <$> (lookup' ns e n) = Some (lookup' ns e' n)) →
        fmapO' ns k e = Some e'.
      Proof. intros. by apply fmapO'_Some. Qed.

      Lemma fmapO'_None
          (k : ∀ (n : name), A n -> option (B n)) (e : to_list' A ns) :
        NoDup ns →
        ns ≠ [] →
        (∃ n, n ∈ ns ∧ (k n) <$> (lookup' ns e n) = Some None) ↔
        fmapO' ns k e = None.
      Proof.
        induction ns as [|n' ns' IH] => /=; [done|].
        intros [NIn ND]%NoDup_cons _.
        destruct e as [fn e'].
        specialize (IH e' ND).
        rewrite bind_None. split.
        - intros (n & Inn & (fn' & EqL & EqN)%bind_Some).
          inversion EqN as [EqN'].
          move : EqL.
          case (decide (n' = n)) => ? /=.
          { subst n. simpl. inversion 1. by left. }
          intros EqL.
          apply elem_of_cons in Inn as [?|Inn]; [by subst n|].
          destruct IH as [IH1 _].
          { clear -Inn. intros ->. by apply not_elem_of_nil in Inn. }
          rewrite IH1.
          + clear. simpl. destruct (k n' fn); naive_solver.
          + exists n. by rewrite EqL /= EqN'.
        - intros [EqN|(gn & EqS & [EqN|(?&?&?)]%bind_None)]; [..|done].
          + exists n'. split; [by left|]. by rewrite decide_True_pi /= EqN.
          + destruct IH as [_ IH2]. { clear -EqN. by intros ->. }
            destruct (IH2 EqN) as (n & Inn & EqN').
            exists n. split; [by right|].
            case_match; [|done].
            subst n'. exfalso. by apply NIn.
      Qed.
    End theory_with_fg.
  End internal.

  Import internal.

  Section with_finite.
    Context `{Finite name}.

    Definition to_list (A : name -> Type) : Type := to_list' A (enum name).

    Definition lookup {A : name -> Type} (e : to_list A) (n : name) : A n
      := is_Some_proj (lookup'_elem_of_Some _ e n (elem_of_enum n)).

    Definition fmap {A B : name -> Type} (k : ∀ (n : name), A n -> B n)
      : to_list A -> to_list B := fmap' (enum name) k.

    Definition fmapO {A B : name -> Type} (k : ∀ (n : name), A n -> option (B n))
      : to_list A -> option (to_list B) := fmapO' (enum name) k.

    Definition update {A : name -> Type} (n : name) (v : A n)
      : to_list A -> to_list A := update' (enum name) n v.

    Lemma lookup_unfold {A : name -> Type} (e : to_list A) (n : name) :
      lookup' (enum name) e n = Some (lookup e n).
    Proof. rewrite /lookup. apply is_Some_proj_eq. Qed.

    Lemma lookup_fmap {A B : name -> Type} (k : ∀ (n : name), A n -> B n)
        (e : to_list A) (n : name) :
      lookup (fmap k e) n = k n (lookup e n).
    Proof. apply Some_inj. by rewrite -lookup_unfold lookup_fmap' lookup_unfold. Qed.

    Lemma fmapO_Some {A B : name -> Type}
        (k : ∀ (n : name), A n -> option (B n))
        (e : to_list A) (e' : to_list B) :
      (∀ n, k n (lookup e n) = Some (lookup e' n)) ↔
      fmapO k e = Some e'.
    Proof.
      rewrite -fmapO'_Some; last by apply NoDup_enum.
      apply forall_proper => n.
      rewrite lookup_unfold /= -lookup_unfold. split.
      - intros ? _. by f_equal.
      - move => /(_ (elem_of_enum _)). naive_solver.
    Qed.

    Lemma fmapO_None {A B : name -> Type}
        (k : ∀ (n : name), A n -> option (B n))
        (e : to_list A) :
      (∃ n, k n (lookup e n) = None) → (* the reverse direction needs [Inhabited name] *)
      fmapO k e = None.
    Proof.
      intros [n Eqn]. apply fmapO'_None.
      - apply NoDup_enum.
      - intros EqN.
        apply (not_elem_of_nil n). rewrite -EqN. apply elem_of_enum.
      - exists n. split; [apply elem_of_enum|]. by rewrite lookup_unfold /= Eqn.
    Qed.

    Lemma lookup_update_eq {A : name -> Type}
        (e : to_list A) (n : name) (v : A n) :
      lookup (update n v e) n = v.
    Proof.
      apply Some_inj. rewrite -lookup_unfold.
      by apply lookup_update'_eq, elem_of_enum.
    Qed.

    Lemma lookup_update_ne {A : name -> Type}
        (e : to_list A) (n : name) (v : A n) :
      ∀ n', n ≠ n' →
      lookup (update n v e) n' = lookup e n'.
    Proof.
      intros. apply Some_inj. rewrite -2!lookup_unfold. by apply lookup_update'_ne.
    Qed.

    Lemma lookup_ext {A : name -> Type} (e e' : to_list A) :
      (∀ n, lookup e n = lookup e' n) → e = e'.
    Proof.
      intros IS. apply lookup'_ext; [apply NoDup_enum|].
      intros. by rewrite 2!lookup_unfold IS.
    Qed.
  End with_finite.

End fin_prod.
