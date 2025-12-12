(*
 * Copyright (c) 2021-2023 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export stdpp.finite.
Require Import bluerock.prelude.base.
Require Import bluerock.prelude.bool.
Require Import bluerock.prelude.numbers.
Require Import bluerock.prelude.list_numbers.
Require Import bluerock.prelude.gmap.
Require Import bluerock.prelude.list.
Require Import bluerock.prelude.fin_sets.
Require Import bluerock.prelude.axioms.funext.

#[local] Open Scope N_scope.

(**
Extensions of [stdpp.finite], especially for variants:

From the [Finite] typeclass, like from Haskell's [Enum], one can generate
conversion to and from [N], both for individual elements and bitsets of them.
*)

(** Enable bidirectional typechecking for [decode_fin] *)
#[global] Arguments decode_fin & {A _ _} i. (* [&] = infer [A] from return type. *)

(** Let [simpl/cbn] not unfold [enum], to avoid bloating goals.
Concrete computations can use decision procedures [vm_decide] or normalization
tactics. *)
#[global] Arguments enum : simpl never.

Section fin_fun_eq_dec.
  Context `{Finite A} `{EqDecision B}.
  Implicit Types (f g : A -> B).

  #[global, refine] Instance fin_fun_eq_dec : EqDecision (A -> B) := fun r1 r2 =>
    cast_if (decide (∀ n, r1 n = r2 n)).
  Proof using Type*.
    abstract by funext.
    abstract by intros ?; subst.
  Defined.

  (* Thanks to [Hedberg]'s theorem ([stdpp.proof_irrel.eq_pi]) and its corollary
  [stdpp.decidable.decide_True_pi], the above use of [functional_extensionality]
  is proof-irrelevant. *)
  #[local] Instance fin_fun_eq_pi f g : ProofIrrel (f = g).
  Proof. apply _. Abort.

  (* Examples using proof irrelevance for functions with finite domains. *)
  #[local] Lemma fin_fun_decide_True_pi f g (E : f = g) :
    decide (f = g) = left E.
  Proof. apply decide_True_pi. Abort.

  #[local] Lemma fin_fun_eq_refl f :
    decide (f = f) = left eq_refl.
  Proof. apply decide_True_pi. Abort.

  Import EqNotations.
  #[local] Lemma fin_fun_eq_refl_transport f g (E : f = g) :
    rew [λ f', {f' = g} + {f' ≠ g}] E in decide (f = g) = left eq_refl.
  Proof. rewrite decide_True_pi. by destruct E. Abort.
End fin_fun_eq_dec.

(** Rewriting-oriented variant of [elem_of_enum]; inspired by [elem_of_top]. *)
Lemma elem_of_enum' `{Finite A} (x : A) :
  x ∈ enum A ↔ True.
Proof. naive_solver eauto using elem_of_enum. Qed.

(* To upstream. *)
#[global] Instance set_unfold_elem_of_enum `{Finite A} (x : A) :
  SetUnfoldElemOf x (enum A) True.
Proof. constructor. by rewrite elem_of_enum'. Qed.

Lemma subset_of_enum `{Finite A} xs :
  xs ⊆ enum A.
Proof. set_solver. Qed.

Lemma elem_of_filter_enum `{Finite A} `{∀ x, Decision (P x)} (a : A) :
  a ∈ filter P (enum A) ↔ P a.
Proof. set_solver. Qed.

Lemma list_find_enum_total `{Finite A} (a : A) :
  is_Some (list_find (a =.) (enum A)).
Proof. apply (list_find_elem_of _ _ a) => //. set_solver. Qed.

(* stdlib adapters *)

Section finite_stdlib.
  Context `{Finite A}.

  Lemma ListNoDup_enum : List.NoDup (enum A).
  Proof. apply NoDup_ListNoDup, NoDup_enum. Qed.

  Lemma list_In_enum x : In x (enum A).
  Proof. apply elem_of_list_In, elem_of_enum. Qed.
End finite_stdlib.

Section finite_preimage.
  Context `{Finite A} `{EqDecision B}.
  Implicit Types (a : A) (b : B) (f : A → B).

  Definition finite_preimage f b : list A := filter (λ a, f a = b) (enum A).

  Lemma elem_of_finite_preimage f a b :
    a ∈ finite_preimage f b ↔ f a = b.
  Proof. apply: elem_of_filter_enum. Qed.

  (** Teach [set_solver] to use [elem_of_finite_preimage]! *)
  #[global] Instance set_unfold_finite_preimage f a b P :
    SetUnfold (f a = b) P →
    SetUnfoldElemOf a (finite_preimage f b) P.
  Proof. split. rewrite elem_of_finite_preimage. set_solver. Qed.

  Lemma finite_preimage_inj_singleton `{!Inj eq eq f} a :
    finite_preimage f (f a) = [a].
  Proof.
    apply list_singleton_eq_ext. { apply NoDup_filter, NoDup_enum. }
    set_solver.
  Qed.

  Definition finite_inverse f b : option A := head $ finite_preimage f b.

  Lemma finite_inverse_Some_inv f a b :
    finite_inverse f b = Some a → f a = b.
  Proof. intros Hof%head_Some_elem_of. set_solver. Qed.

  Lemma finite_inverse_is_Some f a b :
    f a = b → is_Some (finite_inverse f b).
  Proof.
    intros Heq%elem_of_finite_preimage%elem_of_not_nil.
    exact /head_is_Some.
  Qed.

  Lemma finite_inverse_None_equiv f b :
    finite_inverse f b = None ↔ ¬(∃ a, f a = b).
  Proof.
    rewrite eq_None_not_Some. f_equiv.
    split. { intros [a ?%finite_inverse_Some_inv]. by exists a. }
    by intros [a ?%finite_inverse_is_Some].
  Qed.

  #[global] Instance set_unfold_finite_inverse_None f b P :
    (∀ a, SetUnfold (f a = b) (P a)) →
    SetUnfold (finite_inverse f b = None) (¬ (∃ a, P a)).
  Proof. constructor. rewrite finite_inverse_None_equiv. set_solver. Qed.

  Section finite_preimage_inj.
    Context `{Hinj : !Inj eq eq f}.
    #[local] Set Default Proof Using "Type*".

    Lemma finite_inverse_inj_cancel a :
      finite_inverse f (f a) = Some a.
    Proof. by rewrite /finite_inverse finite_preimage_inj_singleton. Qed.

    Lemma finite_inverse_inj_Some_equiv a b :
      finite_inverse f b = Some a ↔ f a = b.
    Proof.
      naive_solver eauto using finite_inverse_Some_inv, finite_inverse_inj_cancel.
    Qed.

    #[global] Instance set_unfold_finite_inverse_inj_Some a b P :
      SetUnfold (f a = b) P →
      SetUnfold (finite_inverse f b = Some a) P.
    Proof. constructor. rewrite finite_inverse_inj_Some_equiv. set_solver. Qed.
  End finite_preimage_inj.
End finite_preimage.

Section finite_preimage_set.
  Context `{FinSet A C} `{FinSet B D}.
  Context `{!Finite A}.
  #[local] Set Default Proof Using "Type*".

  Implicit Types (a : A) (b : B) (f : A → B) (bs : D).

  Definition finite_preimage_set (f : A → B) (bs : D) : C :=
    set_concat_map (finite_preimage f) bs.

  Lemma finite_preimage_set_empty f :
    finite_preimage_set f ∅ ≡ ∅.
  Proof. apply set_concat_map_empty. Qed.

  #[global] Instance finite_preimage_set_proper f :
    Proper (equiv ==> equiv) (finite_preimage_set f).
  Proof. solve_proper. Qed.

  #[global] Instance finite_preimage_set_mono f :
    Proper (subseteq ==> subseteq) (finite_preimage_set f).
  Proof. solve_proper. Qed.

  Lemma elem_of_finite_preimage_set f a bs :
    a ∈ finite_preimage_set f bs ↔ f a ∈ bs.
  Proof. set_solver. Qed.

  #[global] Instance set_unfold_finite_preimage_set f a bs Q :
    SetUnfoldElemOf (f a) bs Q →
    SetUnfoldElemOf a (finite_preimage_set f bs) Q.
  Proof. constructor. rewrite elem_of_finite_preimage_set. set_solver. Qed.

  Lemma finite_preimage_set_union f bs1 bs2 :
    finite_preimage_set f (bs1 ∪ bs2) ≡
    finite_preimage_set f bs1 ∪ finite_preimage_set f bs2.
  Proof. apply set_concat_map_union. Qed.

  Lemma finite_preimage_set_singleton f b :
    finite_preimage_set f {[ b ]} ≡ list_to_set $ finite_preimage f b.
  Proof. apply set_concat_map_singleton. Qed.

  Lemma finite_preimage_set_inj_singleton `{!Inj eq eq f} a :
    finite_preimage_set f {[ f a ]} ≡ {[ a ]}.
  Proof. set_solver. Qed.

  Section finite_preimage_set_leibniz.
    Context `{!LeibnizEquiv C} `{!LeibnizEquiv D}.

    Lemma finite_preimage_set_empty_L f :
      finite_preimage_set f ∅ = ∅.
    Proof. apply set_concat_map_empty_L. Qed.
    Lemma finite_preimage_set_union_L f bs1 bs2 :
      finite_preimage_set f (bs1 ∪ bs2) =
      finite_preimage_set f bs1 ∪ finite_preimage_set f bs2.
    Proof. apply set_concat_map_union_L. Qed.
    Lemma finite_preimage_set_singleton_L f b :
      finite_preimage_set f {[ b ]} = list_to_set $ finite_preimage f b.
    Proof. apply set_concat_map_singleton_L. Qed.
    Lemma finite_preimage_set_inj_singleton_L `{!Inj eq eq f} a :
      finite_preimage_set f {[ f a ]} = {[ a ]}.
    Proof. unfold_leibniz. apply finite_preimage_set_inj_singleton. Qed.
  End finite_preimage_set_leibniz.
End finite_preimage_set.

#[global] Instance finite_preimage_set_params :
  Params (@finite_preimage_set) 12 := {}.

Notation finite_preimage_gset :=
  (finite_preimage_set (C := gset _) (D := gset _)) (only parsing).

Definition encode_N `{Countable A} (x : A) : N :=
  Pos.pred_N (encode x).
Definition decode_N `{Countable A} (i : N) : option A :=
  decode (N.succ_pos i).
#[global] Arguments decode_N : simpl never.

Section countable.
  Context `{Countable A}.
  Implicit Type (x : A).

  #[global] Instance encode_N_inj : Inj (=) (=) (encode_N (A:=A)).
  Proof. unfold encode_N; intros x y Hxy; apply (inj encode); lia. Qed.
  Lemma decode_encode_N x : decode_N (encode_N x) = Some x.
  Proof. rewrite /decode_N /encode_N N_succ_pos_pred. apply decode_encode. Qed.

  Lemma encode_nat_N x : encode_nat x = N.to_nat (encode_N x).
  Proof. rewrite /encode_nat /encode_N. lia. Qed.

  Lemma encode_N_nat x : encode_N x = N.of_nat (encode_nat x).
  Proof. by rewrite encode_nat_N N2Nat.id. Qed.
  Lemma decode_nat_N i : decode_nat i =@{option A} decode_N (N.of_nat i).
  Proof. by rewrite /decode_nat Pos_of_S. Qed.
  Lemma decode_N_nat i : decode_N i =@{option A} decode_nat (N.to_nat i).
  Proof. by rewrite decode_nat_N N2Nat.id. Qed.
End countable.

Definition card_N A `{Finite A} : N := N.of_nat $ card A.

Section finite.
  Context `{Finite A}.
  Implicit Type (x : A).

  Lemma card_N_lengthN : card_N A = lengthN (enum A).
  Proof. by []. Qed.

  (* Unfolding lemma: pretty annoying to prove inline by unfolding. *)
  Lemma finite_decode_nat_unfold n :
    decode_nat n = enum A !! n.
  Proof. apply (f_equal (flip lookup (enum _))). lia. Qed.

  Lemma enum_lookup_encode_nat (x : A) :
    enum A !! encode_nat x = Some x.
  Proof. by rewrite -finite_decode_nat_unfold decode_encode_nat. Qed.

  (* To upstream! Missing companion to [encode_lt_card]. *)
  Lemma finite_decode_nat_lt n x :
    decode_nat n = Some x → (n < card A)%nat.
  Proof. rewrite finite_decode_nat_unfold /card. apply lookup_lt_Some. Qed.

  (** Lift the above lemmas *)
  Lemma finite_decode_N_unfold' n :
    decode_N n = enum A !! N.to_nat n.
  Proof. by rewrite decode_N_nat finite_decode_nat_unfold. Qed.

  Lemma finite_decode_N_unfold n :
    decode_N n = enum A !! n.
  Proof. by rewrite list_lookupN_lookup -finite_decode_N_unfold'. Qed.

  Lemma enum_lookup_encode_N (x : A) :
    enum A !! encode_N x = Some x.
  Proof. by rewrite -finite_decode_N_unfold decode_encode_N. Qed.

  Lemma finite_decode_N_lt n x :
    decode_N n = Some x → n < card_N A.
  Proof. rewrite /card_N decode_N_nat => /finite_decode_nat_lt. lia. Qed.

  Lemma encode_N_lt_card_N x : encode_N x < card_N A.
  Proof. rewrite encode_N_nat. apply N_of_nat_lt_mono, encode_lt_card. Qed.

  Lemma encode_decode_N (i : N) :
    i < card_N A →
    ∃ x : A, decode_N i = Some x ∧ encode_N x = i.
  Proof.
    rewrite /card_N -{1}(N2Nat.id i). intros Hle%N_of_nat_lt_mono.
    have [x [Hdec Henc]] := encode_decode A (N.to_nat i) Hle.
    exists x. rewrite decode_nat_N encode_nat_N N2Nat.id in Hdec Henc.
    by apply (inj N.to_nat) in Henc.
  Qed.

  (** A partial inverse to [decode_encode_N]: if [decode_N] succeeds, we can
  [encode_N] the result back. *)
  Lemma decode_N_Some_encode_N (n : N) (x : A)
    (Hdec : decode_N n = Some x) : encode_N x = n.
  Proof.
    pose proof (finite_decode_N_lt _ _ Hdec) as Hcmp.
    destruct (encode_decode_N _ Hcmp) as (x' & ?Hdec & Henc).
    naive_solver.
  Qed.

  Lemma decode_N_encode_N (n : N) (x : A) :
    decode_N n = Some x ↔ encode_N x = n.
  Proof. naive_solver eauto using decode_encode_N, decode_N_Some_encode_N. Qed.

  #[global] Instance set_unfold_decode_N_Some x n P :
    SetUnfold (encode_N x = n) P →
    SetUnfold (decode_N n = Some x) P.
  Proof. constructor. rewrite decode_N_encode_N. set_solver. Qed.

  Lemma decode_N_None_encode_N (n : N) :
    decode_N (A := A) n = None ↔ ¬(∃ x, encode_N x = n).
  Proof.
    rewrite eq_None_not_Some /is_Some.
    by setoid_rewrite decode_N_encode_N.
  Qed.

  #[global] Instance set_unfold_decode_N_None n P :
    (∀ x, SetUnfold (encode_N x = n) (P x)) →
    SetUnfold (decode_N (A := A) n = None) (¬∃ x, P x).
  Proof. constructor. rewrite decode_N_None_encode_N. set_solver. Qed.

  Lemma decode_N_is_inverse n :
    finite_inverse encode_N n = decode_N (A := A) n.
  Proof. destruct decode_N eqn:?; set_solver. Qed.
End finite.

(* From (pieces of) [Countable] (and more) to [Finite]. *)
Section enc_finite.
  #[local] Close Scope N_scope.
  Context `{EqDecision A}.
  Context (to_nat : A → nat) (of_nat : nat → A) (c : nat).
  Context (of_to_nat : ∀ x, of_nat (to_nat x) = x).
  Context (to_nat_c : ∀ x, to_nat x < c).
  Context (to_of_nat : ∀ i, i < c → to_nat (of_nat i) = i).

  (* Unfolding lemma for enc_finite. *)
  Lemma enc_finite_enum :
    @enum _ _ (enc_finite to_nat of_nat c of_to_nat to_nat_c to_of_nat) = of_nat <$> seq 0 c.
  Proof. done. Qed.
End enc_finite.

(** Lift enc_finite to [N] *)
Section enc_finite_N.
  Context `{Inhabited A}.
  Context `{EqDecision A}.
  Context (to_N : A → N) (of_N : N → option A) (c : N).
  Context (of_to_N : ∀ x, of_N (to_N x) = Some x).

  Context (to_N_c : ∀ x, to_N x < c).
  Context (to_of_N : ∀ i, i < c → to_N (default inhabitant $ of_N i) = i).

  #[program] Definition enc_finite_N : Finite A :=
    enc_finite (N.to_nat ∘ to_N) ((λ x, default inhabitant (of_N x)) ∘ N.of_nat) (N.to_nat c) _ _ _.
  Next Obligation. move=> /= x. by rewrite N2Nat.id of_to_N. Qed.
  Next Obligation. move=> /= x. have := to_N_c x. lia. Qed.
  Next Obligation. move=> /= x Hle. rewrite to_of_N; lia. Qed.
End enc_finite_N.

(** Useful to prove [NoDup] when lifting [Finite] over constructor [f]. *)
Lemma NoDup_app_fmap_l {A B} `{Finite A} (f : A -> B) xs :
  Inj eq eq f →
  NoDup xs →
  (∀ x : B, x ∈ f <$> enum A → x ∉ xs) →
  NoDup ((f <$> enum A) ++ xs).
Proof.
  intros. rewrite NoDup_app. by split_and!; first apply /NoDup_fmap_2 /NoDup_enum.
Qed.

(** Useful to [elem_of_enum] when lifting [Finite] over constructor [f]. *)
Lemma elem_of_app_fmap_enum_l `{Finite A} `(f : A → B) x (ys : list B) :
  f x ∈ (f <$> enum A) ++ ys.
Proof.
  by apply/elem_of_app; left; apply/elem_of_list_fmap_1/elem_of_enum.
Qed.

(**
Module-based infrastructure to generate Finite-based utilities.

Example use for a variant.

Module right.
  Variant _t := FOO | BAR.
  Definition t := _t. (* Workaround Coq bug. *)
  #[global] Instance t_eq_dec : EqDecision t.
  Proof. solve_decision. Defined.

  #[global] Instance t_finite : Finite t.
  Proof. solve_finite [FOO; BAR]. Defined.

  (* Option 1: specify [to_N] by hand:  *)
  Definition to_N : t -> N := ..

  (* get a specialized copy of [of_N] and [of_to_N]. *)
  Include finite_encoded_type_mixin.

  (* Option 2 (alternative to 1):
  INSTEAD OF defining [to_N], obtain it from [Finite], together with various
  other parts of an encoding into bitmasks.
  *)
  Include simple_finite_bitmask_type_mixin.

  (* [simple_finite_bitmask_type_mixin] can almost be replaced by (some subset of), but
  enjoys extra lemmas. *)
  Include finite_type_mixin.
  Include bitmask_type_simple_mixin.
  Include finite_bitmask_type_mixin.
End right.

(* For bitmasks over [simple_finite_bitmask_type_intf]. *)
Module rights := simple_finite_bits rights.
(* Else, for bitmasks over [finite_bitmask_type_intf]. *)
Module rights := finite_bits rights.
*)
Module Type eqdec_type.
  Parameter t : Type.
  #[global] Declare Instance t_eq_dec : EqDecision t.
End eqdec_type.

Module Type finite_type <: eqdec_type.
  Include eqdec_type.
  #[global] Declare Instance t_finite : Finite t.
End finite_type.

(**
To define [finite_type] for enums, the following will work:
<<
#[global] Instance t_finite : Finite t.
Proof. solve_finite [GET; SET]. Defined.
>>

Older option (deprecated: more verbose for no gain):
<<
#[global,program] Instance t_finite : Finite t :=
{ enum := [GET; SET] }.
Next Obligation. solve_finite_nodup. Qed.
Next Obligation. solve_finite_total. Qed.
>>
*)
Ltac solve_finite_nodup := vm_decide.
(* Crucially, [case] does not introduce variables: hence [solve_finite_total]
works even for constructors taking arguments from finite domains. *)
Ltac solve_finite_total := case; vm_decide.

Ltac solve_finite Fields :=
  refine (@Build_Finite _ _ Fields _ _);
  [ abstract solve_finite_nodup
  | abstract solve_finite_total ].

(* Mixin hierarchy 1: given a Finite instance and a [to_N] function, we can
create an [of_N] function. This contains [finite_encoded_type] *)
Module Type finite_encoded_type <: finite_type.
  Include finite_type.
  Parameter to_N : t -> N.
End finite_encoded_type.

Module Type finite_encoded_type_mixin (Import F : finite_encoded_type).
  Definition of_N n := finite_inverse to_N n.

  Lemma of_to_N `[Hinj : !Inj eq eq to_N] (x : t) :
    of_N (to_N x) = Some x.
  Proof. exact: finite_inverse_inj_cancel. Qed.

  Lemma to_of_N (n : N) (x : t) :
    of_N n = Some x → to_N x = n.
  Proof. apply finite_inverse_Some_inv. Qed.
End finite_encoded_type_mixin.

(* Mixin hierarchy 2: *)
Module Type finite_type_mixin (Import F : finite_type).
  (*
  Not marked as an instance because it is derivable.
  It is here just in case some mixin wants it. *)
  Definition t_countable : Countable t := _.

  (* Obtain encoding from [t_finite] *)
  Definition to_N : t -> N := encode_N.
  Definition of_N : N -> option t := decode_N.

  Lemma of_to_N x : of_N (to_N x) = Some x.
  Proof. apply decode_encode_N. Qed.

  Lemma to_of_N n x : of_N n = Some x → to_N x = n.
  Proof. apply decode_N_Some_encode_N. Qed.

  Lemma to_N_lt_card_N x : to_N x < card_N t.
  Proof. exact /encode_N_lt_card_N. Qed.
End finite_type_mixin.

Module Type finite_type_intf := finite_type <+ finite_type_mixin.

(* Interface for the bitmask functions. *)
Module Type bitmask_type (Import F : eqdec_type).
  (**
  Convert [t] to the corresponding bit number.
  [bitmask_type_simple_mixin] sets this to [finite_type.to_N], which is
  not always appropriate when interfacing with outside protocols.
  *)
  Parameter to_bit : t -> N.
End bitmask_type.

Module Type bitmask_type_simple_mixin (Import F : finite_type) (Import FM : finite_type_mixin F).
  (* Here, [to_N] is a valid bit encoding *)
  Definition to_bit := to_N.
  Definition of_bit := of_N.

  Lemma of_to_bit x : of_bit (to_bit x) = Some x.
  Proof. apply of_to_N. Qed.

  Lemma to_of_bit n x : of_bit n = Some x → to_bit x = n.
  Proof. apply to_of_N. Qed.

  Lemma to_bit_lt_card_N x : to_bit x < card_N t.
  Proof. exact /to_N_lt_card_N. Qed.
End bitmask_type_simple_mixin.

Module Type finite_bitmask_type_mixin (Import F : finite_type) (Import B : bitmask_type F).
  Implicit Type (x : t) (m n : N).

  Definition to_bitmask (r : t) : N := 2 ^ to_bit r.

  Lemma to_bitmask_setbit x : to_bitmask x = N.setbit 0 (to_bit x).
  Proof. by rewrite N.setbit_spec'. Qed.

  Definition testbit (mask : N) (x : t) : bool :=
    N.testbit mask (to_bit x).

  Lemma testbit_0 x : testbit 0 x = false.
  Proof. by rewrite /testbit N.bits_0. Qed.

  Lemma testbit_lor m1 m2 x :
    testbit (m1 `lor` m2) x =
    testbit m1 x || testbit m2 x.
  Proof. apply N.lor_spec. Qed.

  Lemma testbit_land m1 m2 x :
    testbit (m1 `land` m2) x =
    testbit m1 x && testbit m2 x.
  Proof. apply N.land_spec. Qed.

  #[global] Instance set_unfold_testbit_lor m1 m2 x P Q :
    SetUnfold (testbit m1 x) P →
    SetUnfold (testbit m2 x) Q →
    SetUnfold (testbit (m1 `lor` m2) x) (P ∨ Q).
  Proof. constructor. rewrite testbit_lor. set_solver. Qed.

  #[global] Instance set_unfold_testbit_land m1 m2 x P Q :
    SetUnfold (testbit m1 x) P →
    SetUnfold (testbit m2 x) Q →
    SetUnfold (testbit (m1 `land` m2) x) (P ∧ Q).
  Proof. constructor. rewrite testbit_land. set_solver. Qed.

  Definition filter (mask : N) (x : t) : list t :=
    if testbit mask x then [x] else [].

  Lemma elem_of_filter m (x y : t) :
    y ∈ filter m x ↔
    x = y ∧ testbit m x.
  Proof. rewrite /filter; case_match; set_solver. Qed.

  (* The high priority is important.
  this is only a fallback after other instances apply. *)
  #[global] Instance set_unfold_filter m x y P Q :
    SetUnfold (x = y) P →
    SetUnfold (testbit m x) Q →
    SetUnfoldElemOf y (filter m x) (P ∧ Q) | 100.
  Proof. constructor. rewrite elem_of_filter. set_solver. Qed.

  Lemma filter_0 x : filter 0 x = [].
  Proof. done. Qed.

  Lemma elem_of_filter_lor m1 m2 (x y : t) :
    y ∈ filter (m1 `lor` m2) x ↔
    y ∈ filter m1 x ∨ y ∈ filter m2 x.
  Proof. set_solver. Qed.

  Lemma elem_of_filter_land m1 m2 (x y : t) :
    y ∈ filter (m1 `land` m2) x ↔
    y ∈ filter m1 x ∧ y ∈ filter m2 x.
  Proof. set_solver. Qed.

  #[global] Typeclasses Opaque filter.
  #[global] Arguments filter : simpl never.

  (** Technically redundant, but a leaf, and it cleans up [set_unfold] output. *)
  #[global] Instance set_unfold_filter_0 m x y :
    SetUnfoldElemOf y (filter 0 x) False.
  Proof. constructor. set_solver. Qed.

  (* Parse a bitmask into a list of flags. *)
  Definition to_list_aux (mask : N) (xs : list t) : list t :=
    xs ≫= filter mask.

  Definition to_list (mask : N) : list t := to_list_aux mask $ enum t.

  Lemma elem_of_to_list x n :
    x ∈ to_list n ↔ testbit n x.
  Proof. set_solver. Qed.

  #[global] Instance set_unfold_elem_of_to_list x n P :
    SetUnfold (testbit n x) P →
    SetUnfoldElemOf x (to_list n) P.
  Proof. constructor. rewrite elem_of_to_list. set_solver. Qed.
  #[global] Typeclasses Opaque to_list.

  Lemma to_list_0 : to_list 0 = [].
  Proof. apply list_empty_eq_ext; set_solver. Qed.

  Lemma elem_of_to_list_0 x :
    x ∈ to_list 0 ↔ False.
  Proof. set_solver. Qed.

  Lemma elem_of_to_list_or x m n :
    x ∈ to_list (m `lor` n) ↔ x ∈ to_list m ∨ x ∈ to_list n.
  Proof. set_solver. Qed.

  Lemma elem_of_to_list_and x m n :
    x ∈ to_list (m `land` n) ↔ x ∈ to_list m ∧ x ∈ to_list n.
  Proof. set_solver. Qed.

  Definition setbit (b : t) (n : N) : N := N.setbit n (to_bit b).
  Notation setbit_alt b n := (N.lor (to_bitmask b) n).

  (* Prevent [set_solver] from exposing the implementation. *)
  #[global] Typeclasses Opaque setbit.
  #[global] Arguments setbit : simpl never.

  Lemma setbit_0 x : setbit x 0 = to_bitmask x.
  Proof. by rewrite to_bitmask_setbit. Qed.
  Lemma setbit_is_alt b n : setbit b n = setbit_alt b n.
  Proof. by rewrite /setbit N.setbit_spec' comm_L. Qed.
  Lemma setbit_not_0 b n : setbit b n ≠ 0.
  Proof.
    rewrite /setbit => Eq0.
    assert (Eqt : N.testbit (N.setbit n (to_bit b)) (to_bit b) = true).
    { apply N.setbit_iff. by left. }
    by rewrite Eq0 N.bits_0 in Eqt.
  Qed.

  Lemma testbit_setbit (x y : t) (mask : N) :
    testbit (setbit x mask) y =
    bool_decide (to_bit x = to_bit y) || testbit mask y.
  Proof. by rewrite /testbit /setbit N_setbit_bool_decide. Qed.

  Lemma testbit_to_bitmask (x z : t) :
    testbit (to_bitmask x) z = bool_decide (to_bit x = to_bit z).
  Proof. by rewrite -setbit_0 testbit_setbit testbit_0 right_id_L. Qed.

  Lemma testbit_to_bitmask_eq (x : t) : testbit (to_bitmask x) x = true.
  Proof.
    Succeed by rewrite testbit_to_bitmask bool_decide_eq_true.
    apply N.pow2_bits_true.
  Qed.

  Section to_bit_inj.
    Context`{Hinj : !Inj eq eq to_bit}.
    #[local] Set Default Proof Using "Hinj".

    Lemma testbit_setbit_inj (x y : t) (mask : N) :
      testbit (setbit x mask) y =
      bool_decide (x = y) || testbit mask y.
    Proof.
      rewrite testbit_setbit. f_equal.
      by rewrite (bool_decide_ext _ _ (inj_iff to_bit _ _)).
    Qed.

    (* We currently offer no [testbit_setbit] instance for the non-Inj case. *)
    #[global] Instance set_unfold_testbit_setbit_inj (x y : t) (mask : N) P Q :
      SetUnfold (x = y) P →
      SetUnfold (testbit mask y) Q →
      SetUnfold (testbit (setbit x mask) y) (P ∨ Q).
    Proof. constructor. rewrite testbit_setbit_inj. set_solver. Qed.

    Lemma testbit_to_bitmask_inj (x z : t) :
      testbit (to_bitmask x) z = bool_decide (x = z).
    Proof. by rewrite testbit_to_bitmask (bool_decide_ext _ _ (inj_iff to_bit _ _)). Qed.

    #[global] Instance set_unfold_testbit_to_bitmask_inj (x z : t) P :
      SetUnfold (x = z) P →
      SetUnfold (testbit (to_bitmask x) z) P.
    Proof. constructor. rewrite testbit_to_bitmask_inj. set_solver. Qed.

    Lemma filter_setbit' (x y z : t) (mask : N) :
      y ∈ filter (setbit x mask) z ↔ y ∈ filter (to_bitmask x) z ∨ y ∈ filter mask z.
    Proof. set_solver. Qed.

    Lemma filter_setbit (x y z : t) (mask : N) :
      y ∈ filter (setbit x mask) z ↔ x = y ∧ y = z ∨ y ∈ filter mask z.
    Proof. set_solver. Qed.

    Lemma to_list_setbit (x z : t) (mask : N) :
      z ∈ to_list (setbit x mask) ↔ z = x ∨ z ∈ to_list mask.
    Proof. set_solver. Qed.
  End to_bit_inj.
End finite_bitmask_type_mixin.

Module Type finite_bitmask_type_intf := finite_type <+ bitmask_type <+ finite_bitmask_type_mixin.

(* All the above mixins in the right order, for when [bitmask_type_simple_mixin]
is appropriate. *)
Module Type simple_finite_bitmask_type_mixin (Import F : finite_type).
  Include finite_type_mixin F.
  Include bitmask_type_simple_mixin F.
  Include finite_bitmask_type_mixin F.

  Definition all_bits : N := N.ones (N.of_nat (card F.t)).

  (* Cannot be proven in [finite_bitmask_type_mixin] because we need [to_bit]'s
  definition. *)
  Lemma to_list_max : to_list all_bits = enum F.t.
  Proof.
    rewrite /to_list /to_list_aux /filter /mbind.
    elim: enum => [//|x xs IH]; cbn; rewrite {}IH.
    set c := testbit _ _; suff -> : c = true by []; rewrite {}/c.
    apply N.ones_spec_iff, encode_N_lt_card_N.
  Qed.
End simple_finite_bitmask_type_mixin.

Module Type simple_finite_bitmask_type_intf := finite_type <+ simple_finite_bitmask_type_mixin.

(* A type for _sets_ of flags, as opposed to the type of flags described above. *)
Module Type finite_bits_aux (BT : finite_bitmask_type_intf).
  Definition t := gset BT.t.
  #[global] Instance top_t : Top t := fin_to_set BT.t (C := t).

  #[global] Instance topset_t : TopSet BT.t t.
  Proof. split. apply _. apply elem_of_fin_to_set. Qed.

  Implicit Type (x : BT.t) (m n : N).
  (*
  [to_bits] and [of_bits] implement a bitset encoding of [t] into N, given
  the encoding [to_bit : BT.t -> N].

  [to_of_bits] and [of_to_bits] show they're inverses, the latter assuming
  [Inj eq eq BT.to_bit].
  *)
  Definition of_bits (mask : N) : t := list_to_set $ BT.to_list mask.

  Lemma elem_of_of_bits x n :
    x ∈ of_bits n ↔ BT.testbit n x.
  Proof. set_solver. Qed.

  #[global] Instance set_unfold_elem_of_to_list x n P :
    SetUnfold (BT.testbit n x) P →
    SetUnfoldElemOf x (of_bits n) P.
  Proof. constructor. rewrite elem_of_of_bits. set_solver. Qed.
  #[global] Typeclasses Opaque of_bits.

  Lemma of_bits_0 : of_bits 0 = ∅.
  Proof. set_solver. Qed.

  Lemma of_bits_or m n : of_bits (m `lor` n) = of_bits m ∪ of_bits n.
  Proof. set_solver. Qed.

  Lemma of_bits_and m n : of_bits (m `land` n) = of_bits m ∩ of_bits n.
  Proof. set_solver. Qed.

  Definition to_bits (rs : t) : N := set_fold BT.setbit 0 rs.

  Lemma to_bits_empty : to_bits ∅ = 0.
  Proof. apply set_fold_empty. Qed.
  Lemma to_bits_singleton x : to_bits {[x]} = BT.to_bitmask x.
  Proof. by rewrite /to_bits set_fold_singleton BT.setbit_0. Qed.

  Module Import internal.
    Definition to_bits_alt (rs : t) : N := set_fold (λ b n, BT.setbit_alt b n) 0 rs.
    Lemma to_bits_is_alt rs : to_bits rs = to_bits_alt rs.
    Proof. apply: foldr_ext => // b a. apply BT.setbit_is_alt. Qed.

    (**
    Writing [to_bits] as a commutative, associative fold
    allows reasoning with lemmas about [foldr] and [Permutation].
    See for instance [to_bits_union_singleton]. *)
    Definition to_bits_comm (rs : t) : N :=
      foldr N.lor 0 (BT.to_bitmask <$> elements rs).
    Lemma to_bits_is_comm rs : to_bits rs = to_bits_comm rs.
    Proof. rewrite to_bits_is_alt. apply symmetry, foldr_fmap. Qed.

    (*
    We could also use

    Definition to_bits_comm' (rs : t) : N :=
      set_fold N.lor 0 (set_map (D := gset N) BT.to_bitmask rs).

    But it seems that more lemmas are available on the [foldr] form.
    *)
  End internal.

  (** Internal; [to_bits_union_singleton] is strictly stronger. *)
  #[local] Lemma to_bits_union_singleton_aux x xs (Hni : x ∉ xs) :
    to_bits ({[x]} ∪ xs) = N.lor (BT.to_bitmask x) (to_bits xs).
  Proof. by rewrite !to_bits_is_comm /to_bits_comm elements_union_singleton. Qed.

  Lemma setbit_in_idemp x xs
    (Hin : x ∈ xs) :
    BT.setbit x (to_bits xs) = to_bits xs.
  Proof.
    apply /symmetry /N.bits_inj_iff => i.
    rewrite N_setbit_bool_decide.
    case_bool_decide as Hdec; last reflexivity. rewrite -{}Hdec /=.
    induction xs as [|y ys Hni IHys] using set_ind_L; first by set_solver.
    rewrite to_bits_union_singleton_aux // N.lor_spec orb_true_iff.
    move: Hin => /elem_of_union [{IHys} /elem_of_singleton -> | Hin]; [left|right].
    { apply BT.testbit_to_bitmask_eq. }
    { exact: IHys. }
  Qed.

  (** The right-hand side matches [to_bits_comm]'s definition. *)
  Lemma to_bits_union_singleton x xs :
    to_bits ({[x]} ∪ xs) = N.lor (BT.to_bitmask x) (to_bits xs).
  Proof.
    destruct (decide (x ∈ xs)). 2: exact: to_bits_union_singleton_aux.
    rewrite subseteq_union_1_L; [|set_solver].
    by rewrite -BT.setbit_is_alt setbit_in_idemp.
  Qed.

  Lemma to_bits_non_empty xs : xs ≠ ∅ ↔ to_bits xs ≠ 0.
  Proof.
    induction xs as [|??? IHxs] using set_ind_L. { by rewrite to_bits_empty. }
    rewrite to_bits_union_singleton -BT.setbit_is_alt.
    split => ?; [|set_solver]. apply BT.setbit_not_0.
  Qed.

  Lemma to_bits_testbit xs x :
    BT.testbit (to_bits xs) x
    -> ∃ y, y ∈ xs ∧ BT.to_bit x = BT.to_bit y.
  Proof.
    induction xs as [|y ?? IHxs] using set_ind_L.
    { by rewrite to_bits_empty BT.testbit_0. }
    rewrite to_bits_union_singleton BT.testbit_lor orb_True.
    intros [EQy|EQX].
    - rewrite BT.testbit_to_bitmask Is_true_eq bool_decide_eq_true in EQy.
      exists y. set_solver.
    - destruct (IHxs EQX) as (y' & ? & ?).
      exists y'. set_solver.
  Qed.

  Lemma to_bits_testbit_elem_of x xs :
    x ∈ xs -> BT.testbit (to_bits xs) x.
  Proof.
    induction xs as [|y ?? IHxs] using set_ind_L.
    { by rewrite to_bits_empty BT.testbit_0. }
    rewrite to_bits_union_singleton BT.testbit_lor orb_True.
    rewrite elem_of_union elem_of_singleton.
    intros [->|EQX].
    - left. apply Is_true_eq, BT.testbit_to_bitmask_eq.
    - right. by apply IHxs.
  Qed.

  Lemma to_bits_union xs ys :
    to_bits (xs ∪ ys) = N.lor (to_bits xs) (to_bits ys).
  Proof.
    induction xs as [|??? IHxs] using set_ind_L. { by rewrite to_bits_empty !left_id_L. }
    by rewrite -(assoc_L _ {[x]}) !to_bits_union_singleton IHxs assoc_L.
  Qed.

  Lemma to_bitmask_land_neq `{INJ : !Inj eq eq BT.to_bit} x y (N : x <> y) :
    BT.to_bitmask x `land` BT.to_bitmask y = 0.
  Proof.
    apply N.bits_inj_iff => i; rewrite N.land_spec N.bits_0.
    have X: BT.to_bit x <> BT.to_bit y by move/INJ.
    rewrite 2!BT.to_bitmask_setbit.
    move: X; move: (BT.to_bit x); move: (BT.to_bit y) => a b X.
    rewrite 2!N.setbit_eqb !N_eqb_bool_decide.
    destruct (bool_decide_reflect (b = i)); destruct (bool_decide_reflect (a = i)) => //=.
    subst; contradiction.
  Qed.

  Lemma to_bits_intersection_singleton `{INJ : !Inj eq eq BT.to_bit} xs y :
    to_bits (xs ∩ {[y]}) = N.land (to_bits xs) (to_bits {[y]}).
  Proof.
    induction xs as [|??? IHxs] using set_ind_L.
    { by rewrite intersection_empty_l_L to_bits_empty N.land_0_l. }
    rewrite intersection_comm_L intersection_union_l_L 2!to_bits_union.
    rewrite [_ ∩ X]intersection_comm_L IHxs N.land_lor_distr_l.
    destruct (bool_decide_reflect (y = x)).
    { subst x. rewrite intersection_singletons_L. f_equal. by rewrite N.land_diag. }
    have ->: ({[y]} : t) ∩ {[x]} = ∅ by set_solver.
    rewrite 2!to_bits_singleton to_bits_empty to_bitmask_land_neq; last by [].
    by [].
  Qed.

  Lemma to_bits_intersection `{INJ : !Inj eq eq BT.to_bit} xs ys :
    to_bits (xs ∩ ys) = N.land (to_bits xs) (to_bits ys).
  Proof.
    induction xs as [|??? IHxs] using set_ind_L.
    { by rewrite intersection_empty_l_L to_bits_empty N.land_0_l. }
    rewrite intersection_comm_L intersection_union_l_L 2!to_bits_union.
    rewrite [_ ∩ X]intersection_comm_L IHxs N.land_lor_distr_l.
    rewrite to_bits_intersection_singleton. f_equal. by rewrite N.land_comm.
  Qed.


  (* ys is partial surjective on xs, if ys contains any element x in xs
  that has the same bit encoding as an element y in ys. *)
  Definition partial_surjective (xs ys : t) : Prop :=
    ∀ x y, x ∈ xs -> y ∈ ys -> BT.to_bit x = BT.to_bit y -> x ∈ ys.

  Lemma of_bits_partial_surjective xs n :
    partial_surjective xs (of_bits n).
  Proof.
    rewrite /partial_surjective => x y.
    rewrite !elem_of_of_bits => Inxs Inn EQb.
    by rewrite /BT.testbit EQb.
  Qed.

  Lemma top_partial_surjective xs : partial_surjective xs ⊤.
  Proof. rewrite /partial_surjective. intros. by apply elem_of_top. Qed.

  (* Stronger version of [to_bits_intersection]. *)
  Lemma to_bits_intersection_partial_surjective xs ys :
    partial_surjective xs ys ->
    to_bits (xs ∩ ys) = N.land (to_bits xs) (to_bits ys).
  Proof.
    rewrite /partial_surjective.
    induction xs as [|??? IHxs] using set_ind_L.
    { by rewrite intersection_empty_l_L to_bits_empty N.land_0_l. }
    intros INJ.
    rewrite intersection_comm_L intersection_union_l_L 2!to_bits_union.
    rewrite [_ ∩ X]intersection_comm_L IHxs; last first.
    { set_solver. }
    rewrite N.land_lor_distr_l.
    rewrite to_bits_singleton.
    case (decide (x ∈ ys)) => INys.
    - rewrite (_ : ys ∩ {[x]} = {[x]}); last set_solver+INys.

      have EQT := BT.testbit_land (BT.to_bitmask x) (to_bits ys) x.
      rewrite BT.testbit_to_bitmask_eq left_id_L in EQT.

      destruct (N_land_bit (BT.to_bit x) (to_bits ys)) as [EQb|EQ0]; last first.
      { rewrite -/(BT.to_bitmask x) N.land_comm in EQ0.
        rewrite EQ0 BT.testbit_0 in EQT.
        symmetry in EQT.
        apply to_bits_testbit_elem_of, Is_true_eq in INys.
        by rewrite EQT in INys. }
      rewrite -/(BT.to_bitmask x) N.land_comm in EQb.
      by rewrite EQb to_bits_singleton.

    - rewrite (_: ys ∩ {[x]} = ∅); last set_solver+INys.
      rewrite to_bits_empty N.lor_0_l.

      destruct (N_land_bit (BT.to_bit x) (to_bits ys)) as [EQb|EQ0]; last first.
      { rewrite -/(BT.to_bitmask x) N.land_comm in EQ0.
        by rewrite EQ0 N.lor_0_l. }
      exfalso.
      rewrite N.land_comm -/(BT.to_bitmask x) in EQb.

      have EQT := BT.testbit_land (BT.to_bitmask x) (to_bits ys) x.
      rewrite EQb BT.testbit_to_bitmask_eq left_id_L in EQT.
      symmetry in EQT.
      apply Is_true_eq, to_bits_testbit in EQT as (y & INy & EQy).
      apply INys, (INJ x y ltac:(set_solver-) INy EQy).
  Qed.

  Lemma of_to_bits_superseteq_singleton x :
    {[x]} ⊆ of_bits (to_bits {[x]}).
  Proof.
    set_unfold=> ?->.
    rewrite to_bits_singleton BT.testbit_to_bitmask bool_decide_true //.
  Qed.

  Lemma of_to_bits_superseteq xs :
    xs ⊆ of_bits (to_bits xs).
  Proof.
    induction xs as [|??? IHxs] using set_ind_L.
    - set_solver.
    - rewrite to_bits_union of_bits_or.
      apply union_mono; [|done]. apply of_to_bits_superseteq_singleton.
  Qed.

  Lemma of_to_bits_top : of_bits (to_bits ⊤) = ⊤.
  Proof. apply (anti_symm (⊆)); [set_solver|apply of_to_bits_superseteq]. Qed.

  (* TODO move [setbit], and these lemmas, with [BT.testbit]. *)
  Section BT_to_bit_inj.
    Context`{Hinj : !Inj eq eq BT.to_bit}.
    #[local] Set Default Proof Using "Hinj".

    Lemma of_bits_setbit x xs :
      of_bits (BT.setbit x xs) = {[x]} ∪ of_bits xs.
    Proof. set_solver. Qed.

    Lemma of_to_bits rs :
      of_bits (to_bits rs) = rs.
    Proof.
      induction rs as [|x xs Hni IHxs] using set_ind_L.
      { by rewrite to_bits_empty of_bits_0. }
      rewrite to_bits_union_singleton -BT.setbit_is_alt.
      by rewrite of_bits_setbit IHxs.
    Qed.

    Lemma of_bits_singleton x : {[x]} = of_bits $ BT.to_bitmask x.
    Proof.
      rewrite -[ {[_]} ]of_to_bits.
      by f_equal; apply: to_bits_singleton.
    Qed.

    #[global] Instance of_to_bits_cancel : Cancel eq of_bits to_bits :=
      of_to_bits.
    #[global] Instance to_bits_inj : Inj eq eq to_bits := cancel_inj.
    #[global] Instance of_bits_surj : Surj eq of_bits := cancel_surj.
  End BT_to_bit_inj.

  Definition masked (mask : N) (x : t) : t :=
    x ∩ of_bits mask.
  Definition masked_opt (mask : N) (x : t) : option t :=
    let res := masked mask x in
    guard (res <> ∅);; Some res.

  Lemma masked_0 rights : masked 0 rights = ∅.
  Proof. by rewrite /masked of_bits_0 right_absorb_L. Qed.

  Lemma masked_opt_0 rights : masked_opt 0 rights = None.
  Proof. by rewrite /masked_opt masked_0. Qed.

  Lemma masked_empty n : masked n ∅ = ∅.
  Proof. rewrite /masked. set_solver. Qed.

  Lemma masked_opt_empty n : masked_opt n ∅ = None.
  Proof. by rewrite /masked_opt masked_empty. Qed.

  Lemma masked_opt_Some_subseteq n xs xs' :
    masked_opt n xs = Some xs' -> xs' ⊆ xs.
  Proof.
    rewrite /masked_opt.
    case (decide (masked n xs = ∅)) => EQE.
    { rewrite option_guard_False //. naive_solver. }
    rewrite option_guard_True //.
    intros; simplify_eq.
    rewrite /masked. apply intersection_subseteq_l.
  Qed.

  (* Warning: prefer [BT.all_bits] if available, that's simpler to reason about. *)
  Definition mask_top : N := to_bits ⊤.

  Lemma masked_top rights :
    masked mask_top rights = rights.
  Proof. rewrite /masked /mask_top of_to_bits_top. set_solver. Qed.

  Lemma masked_opt_top
    rights (Hrights : rights ≠ ∅) :
    masked_opt mask_top rights = Some rights.
  Proof. by rewrite /masked_opt masked_top option_guard_True. Qed.

  Lemma mask_top_land_to_bits xs :
    mask_top `land` to_bits xs = to_bits xs.
  Proof.
    rewrite N.land_comm -to_bits_intersection_partial_surjective.
    - by rewrite right_id_L.
    - apply top_partial_surjective.
  Qed.

  Lemma elem_of_masked mask r rs :
    r ∈ rs → r ∈ of_bits mask → r ∈ masked mask rs.
  Proof. intros. exact /elem_of_intersection. Qed.

  Lemma N_testbit_to_bits rs i :
    N.testbit (to_bits rs) i =
    bool_decide (∃ r, BT.to_bit r = i ∧ r ∈ rs).
  Proof.
    induction rs as [|r rs Hni IHrs] using set_ind_L. {
      rewrite to_bits_empty N.bits_0 bool_decide_eq_false_2 //.
      set_solver. }
    rewrite to_bits_union_singleton N.lor_spec (comm_L orb).
    rewrite {}IHrs.
    case: (bool_decide_reflect (∃ r, _ ∧ r ∈ rs)) => Hdec /=. {
      rewrite bool_decide_eq_true_2 //. set_solver.
    }
    rewrite BT.to_bitmask_setbit.
    rewrite N_setbit_bool_decide N.bits_0 right_id_L.
    apply bool_decide_ext. set_solver.
  Qed.

  Lemma N_testbit_mask_top_to_bit i :
    N.testbit mask_top i = bool_decide (∃ r : BT.t, BT.to_bit r = i).
  Proof.
    rewrite /mask_top /to_bits N_testbit_to_bits.
    apply bool_decide_ext. set_solver.
  Qed.

  Lemma to_of_bits mask :
    to_bits (of_bits mask) = N.land mask_top mask.
  Proof.
    apply N.bits_inj_iff => i.
    rewrite N.land_spec N_testbit_mask_top_to_bit N_testbit_to_bits.
    rewrite -(bool_decide_Is_true (N.testbit _ _)) -bool_decide_and /is_Some.
    apply bool_decide_ext. set_solver.
  Qed.

  Lemma to_bits_inv_singleton `{INJ : !Inj eq eq BT.to_bit} r rs
      (X : to_bits rs `land` BT.to_bitmask r <> 0%N) :
    r ∈ rs.
  Proof.
    rewrite -to_bits_singleton -to_bits_intersection in X.
    destruct (bool_decide_reflect (r ∈ rs)) => //.
    have H: rs ∩ {[r]} = ∅ by set_solver.
    by rewrite H to_bits_empty in X.
  Qed.

  Lemma to_bits_inv_singleton_ne `{INJ : !Inj eq eq BT.to_bit} r rs
      (X : to_bits rs `land` BT.to_bitmask r = 0%N) :
    r ∉ rs.
  Proof.
    rewrite -to_bits_singleton -to_bits_intersection -to_bits_empty in X.
    by apply to_bits_inj in X; set_solver.
  Qed.

  Lemma to_bits_inv_singleton_Z `{INJ : !Inj eq eq BT.to_bit} r rs
      (X : (Z.of_N (to_bits rs) `land` BT.to_bitmask r)%Z <> 0%Z) :
    r ∈ rs.
  Proof.
    rewrite N2Z_land in X; apply to_bits_inv_singleton.
    by move => Y; apply: X; rewrite Y.
  Qed.

  Lemma to_bits_inv_singleton_ne_Z `{INJ : !Inj eq eq BT.to_bit} r rs
      (X : (Z.of_N (to_bits rs) `land` BT.to_bitmask r)%Z = 0%Z) :
    r ∉ rs.
  Proof. rewrite N2Z_land in X; apply to_bits_inv_singleton_ne; lia. Qed.
End finite_bits_aux.

Module Type simple_finite_bits_aux (BT : simple_finite_bitmask_type_intf).
  Include finite_bits_aux BT.

  Lemma of_bits_max : of_bits BT.all_bits = ⊤.
  Proof. by rewrite /of_bits BT.to_list_max. Qed.

  Lemma masked_max rights :
    masked BT.all_bits rights = rights.
  Proof. rewrite /masked of_bits_max. set_solver. Qed.

  Lemma masked_opt_max rights (Hrights : rights ≠ ∅) :
    masked_opt BT.all_bits rights = Some rights.
  Proof. by rewrite /masked_opt masked_max option_guard_True. Qed.

  Lemma N_testbit_all_bits i :
    N.testbit BT.all_bits i = bool_decide (i < card_N BT.t).
  Proof. apply N_ones_spec. Qed.

  Lemma N_testbit_to_bits' rs i :
    N.testbit (to_bits rs) i =
    bool_decide (∃ r, BT.of_bit i = Some r ∧ r ∈ rs).
  Proof.
    rewrite N_testbit_to_bits; apply bool_decide_ext.
    split; intros (r & Heq & Hin); exists r; subst.
    { split; [|done]. exact: BT.of_to_bit. }
    by rewrite (BT.to_of_bit _ _ Heq).
  Qed.

  Lemma N_testbit_to_bits_high_false i X :
    card_N BT.t ≤ i →
    N.testbit (to_bits X) i = false.
  Proof.
    intros Hi. induction X as [|x X _] using set_ind_L; first done.
    rewrite to_bits_union_singleton -BT.setbit_is_alt /BT.setbit.
    rewrite (N.setbit_neq _ (BT.to_bit x) i) -?{}IHX //.
    apply /N.lt_neq /(N.lt_le_trans _ (card_N BT.t)) /Hi.
    exact /BT.to_bit_lt_card_N.
  Qed.

  Lemma to_bits_mod_pow2 X m :
    card_N BT.t ≤ m →
    to_bits X `mod` 2 ^ m = to_bits X.
  Proof.
    intros Hm. apply N_ext_iff => i.
    case: (N.lt_ge_cases i m) => Hi; first by rewrite N.mod_pow2_bits_low.
    rewrite !N.mod_pow2_bits_high // N_testbit_to_bits_high_false //; lia.
  Qed.

  Lemma N_testbit_mask_top_of_bit i :
    N.testbit mask_top i = bool_decide (is_Some (BT.of_bit i)).
  Proof.
    rewrite N_testbit_mask_top_to_bit /is_Some.
    apply bool_decide_ext. set_solver.
  Qed.

  Lemma all_bits_mask_top : BT.all_bits = mask_top.
  Proof.
    apply N.bits_inj_iff => i.
    rewrite N_testbit_all_bits N_testbit_mask_top_of_bit /is_Some.
    apply bool_decide_ext.
    split. {
      intros (x & Hdec & Henc)%encode_decode_N.
      by exists x; apply Hdec.
    }
    by intros (x & Hdec%finite_decode_N_lt).
  Qed.

  Lemma land_mask_idemp {mask_n r} :
    mask_n = mask_top `land` mask_n →
    (* ^^ Check all mask bits are valid! *)
    of_bits mask_n ⊆ r →
    (* ^^ Check [mask_n] is included in [r] *)
    mask_n = (to_bits r `land` mask_n)%N.
  Proof.
    move=> E Hs. rewrite {}E -(to_of_bits mask_n) -to_bits_intersection.
    by rewrite (comm_L _ r) subseteq_intersection_1_L.
  Qed.
End simple_finite_bits_aux.

(* Lift [finite_bits_aux] and [simple_finite_bits_aux] to a module, usable for application. *)
Module finite_bits (BT : finite_bitmask_type_intf).
  Include finite_bits_aux BT.
End finite_bits.
Module simple_finite_bits (BT : simple_finite_bitmask_type_intf).
  Include simple_finite_bits_aux BT.
End simple_finite_bits.

#[program]
Definition enum_empty_dec T `{Finite T} :
  (T * (enum T <> [])) + ((T -> False) * (enum T = [])) :=
  let Ht : ∀ x : T, x ∈ enum T := elem_of_enum in
  let xs := enum T in
  match xs as xs0 return (∀ x : T, x ∈ xs0) -> (T * (xs0 ≠ []) + ((T → False) * (xs0 = []))) with
  | [] => λ Ht, inr ((λ x, _ (Ht x)), eq_refl)
  | x :: xs => λ _, inl (x, _)
  end Ht.
Next Obligation. set_solver. Qed.
Next Obligation. done. Qed.
