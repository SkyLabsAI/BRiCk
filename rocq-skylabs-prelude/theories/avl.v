(*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import Stdlib.Structures.OrderedType.
Require Import Stdlib.FSets.FMapAVL.
Require Import stdpp.fin_maps.
Require Import stdpp.strings.
Require Import bluerock.prelude.base.
Require Import bluerock.prelude.bytestring.	(* backwards compatibility *)

#[local] Set Printing Coercions.

(** TODO: Misplaced *)
Lemma fold_left_cons {A B : Type} (l1 l2 : list (A * B)) :
  fold_left (fun acc e => (e.1, e.2) :: acc) l1 l2 = rev l1 ++ l2.
Proof. clear.
  revert l2; induction l1 as [|e l IH] => l2 /=; first done.
  rewrite IH -app_assoc /=. do 2 f_equal. by destruct e.
Qed.

(**
Unfortunately FMapAVL does not offer module types for the results of
applying its functors. We capture what we need.
*)

Module FMapExtra.

  Module Type LEIBNIZ_EQ (T : Equalities.Eq).
    Parameter eqL : forall a b, T.eq a b -> a = b.
  End LEIBNIZ_EQ.

  Module Type RAW (Key : OrderedType).

    Notation key := Key.t.

    Inductive tree {elt : Type} : Type :=
    | Leaf
    | Node (l : tree) (k : key) (e : elt) (r : tree) (height : Z).
    #[global] Arguments tree : clear implicits.

    Notation t := tree.

    Section ops.
      Context {elt : Type}.
      #[local] Notation t := (t elt).

      Parameter height : t -> Z.
      Parameter cardinal : t -> nat.
      Parameter empty : t.
      Parameter is_empty : t -> bool.
      Parameter mem : key -> t -> bool.
      Parameter find : key -> t -> option elt.
      Parameter create : t -> key -> elt -> t -> t.
      Parameter bal : t -> key -> elt -> t -> t.
      Parameter add : key -> elt -> t -> t.
      Parameter remove_min : t -> key -> elt -> t -> t * (key * elt).
      Parameter merge : t -> t -> t.
      Parameter remove : key -> t -> t.
      Parameter join : t -> key -> elt -> t -> t.
      Record triple := mktriple { t_left : t; t_opt : option elt; t_right : t }.
      Parameter split : key -> t -> triple.
      Parameter concat : t -> t -> t.
      Parameter elements_aux : list (key * elt) -> t -> list (key * elt).
      Parameter elements : t -> list (key * elt).
      Parameter fold : ∀ {A}, (key -> elt -> A -> A) -> t -> A -> A.
      Parameter equal : (elt -> elt -> bool) -> t -> t -> bool.
    End ops.

    Parameter map : ∀ {elt elt'}, (elt -> elt') -> t elt -> t elt'.
    Parameter mapi : ∀ {elt elt'}, (key -> elt -> elt') -> t elt -> t elt'.
    Parameter map_option : ∀ {elt elt'}, (key -> elt -> option elt') -> t elt -> t elt'.
    Parameter map2_opt : ∀ {elt elt' elt''},
      (key -> elt -> option elt' -> option elt'') -> (t elt -> t elt'') -> (t elt' -> t elt'') ->
      t elt -> t elt' -> t elt''.
    Parameter map2 : ∀ {elt elt' elt''}, (option elt -> option elt' -> option elt'') ->
      t elt -> t elt' -> t elt''.

    Section bst.
      Context {elt : Type}.
      #[local] Notation t := (t elt).

      Inductive In (x : key) : t -> Prop :=
      | InRoot l r h y e : Key.eq x y -> In x (Node l y e r h)
      | InLeft l r h y e' : In x l -> In x (Node l y e' r h)
      | InRight l r h y e' : In x r -> In x (Node l y e' r h).

      Definition lt_tree (x : key) (m : t) : Prop := ∀ y, In y m -> Key.lt y x.
      Definition gt_tree (x : key) (m : t) : Prop := ∀ y, In y m -> Key.lt x y.

      Inductive bst : t -> Prop :=
      | BSLeaf : bst Leaf
      | BSNode x e l r h :
        bst l -> bst r ->
        lt_tree x l -> gt_tree x r -> bst (Node l  x e r h).
    End bst.

    Module Proofs.
      Module MX := OrderedTypeFacts Key.
      (**
      NOTE: There's more here that may someday be useful.
      *)
    End Proofs.

  End RAW.

  Module Type MAP (Key : OrderedType).

    Declare Module Raw : RAW Key.

    #[universes(template)]
    Record bst {elt} := Bst {
      this :> Raw.tree elt;
      is_bst : Raw.bst this;
    }.
    #[global] Arguments bst : clear implicits.

    Include FMapInterface.S
      with Module E := Key
      with Definition t := bst.
  End MAP.

  Module Type MIXIN (Key : OrderedType) (Map : MAP Key).

    #[local] Notation K := Key.t.

    Section raw.
      Context {A : Type}.
      #[local] Notation M := (Map.Raw.t A).

      #[global] Instance raw_empty : Empty M := Map.Raw.empty.
      #[global] Instance raw_insert : Insert K A M := Map.Raw.add.
      #[global] Instance raw_delete : Delete K M := Map.Raw.remove.
      #[global] Instance raw_lookup : Lookup K A M := Map.Raw.find.
      #[global] Instance raw_mapfold : MapFold K A M := fun B f b m =>
        Map.Raw.fold f m b.
      #[global] Instance raw_singleton : SingletonM K A M := fun k a =>
        <[ k := a ]> ∅.
    End raw.
    #[global] Instance raw_map : FMap Map.Raw.t := @Map.Raw.map.
    #[global] Instance raw_merge : Merge Map.Raw.t := @Map.Raw.map2.
    #[global] Instance raw_omap : OMap Map.Raw.t := fun _ _ f =>
      Map.Raw.map_option (fun k v => f v).

    Section map.
      Context {A : Type}.
      #[local] Notation M := (Map.t A).

      #[global] Instance map_empty : Empty M := @Map.empty _.
      #[global] Instance map_insert : Insert K A M := @Map.add _.
      #[global] Instance map_delete : Delete K M := @Map.remove _.
      #[global] Instance map_lookup : Lookup K A M := @Map.find _.
      #[global] Instance map_mapfold : MapFold K A M := fun B f b m =>
        Map.fold f m b.
      #[global] Instance map_singleton : SingletonM K A M := fun k a =>
        <[ k := a ]> ∅.

      (**
      TODO: more efficient implementation, doing a single tree traversal
      (like in stdpp), not one for lookup and one for insertion.
      *)
      #[global] Instance map_partial_alter : PartialAlter K A M := fun f k m =>
        match f (m !! k) with
        | Some a => <[ k := a ]> m
        | None => delete k m
        end.
    End map.
    #[global] Instance map_map : FMap Map.t := @Map.map.
    #[global] Instance map_merge : Merge Map.t := Map.map2.
    (**
    TODO:
    #[global] Instance map_omap : OMap Map.t.
    #[global] Instance map_fin_map : FinMap K Map.t.
    *)

    (** ** Canonicalize proofs *)
    Section canon.
      Context {A : Type}.

      #[local] Instance key_lt_dec : RelDecision Key.lt := Map.Raw.Proofs.MX.lt_dec.
      #[local] Instance key_eq_dec : RelDecision Key.eq := Map.Raw.Proofs.MX.eq_dec.

      Fixpoint check_canon (min max : option K) (t : Map.Raw.t A) {struct t} : bool :=
        match t with
        | Map.Raw.Leaf => true
        | Map.Raw.Node l k v r h =>
          check_canon min (Some k) l &&
          check_canon (Some k) max r &&
          match min with
          | None => true
          | Some bot => bool_decide (Key.lt bot k)
          end &&
          match max with
          | None => true
          | Some top => bool_decide (Key.lt k top)
          end
        end.

      Lemma check_canonP t min max :
        check_canon min max t ->
        Map.Raw.bst t /\
        match min with
        | None => True
        | Some bot => Map.Raw.gt_tree bot t
        end /\
        match max with
        | None => True
        | Some top => Map.Raw.lt_tree top t
        end.
      Proof.
        move: min max. induction t as [|l IHl k v r IHr h]=>min max /= Hc.
        { repeat constructor.
          - destruct min; repeat constructor.
            red. inversion 1.
          - destruct max; repeat constructor.
            red. inversion 1. }
        apply andb_prop_elim in Hc. destruct Hc as (Hc & Hmax).
        apply andb_prop_elim in Hc. destruct Hc as (Hc & Hmin).
        apply andb_prop_elim in Hc. destruct Hc as (Hl & Hr).
        destruct (IHl _ _ Hl) as (Hlt & Hlmin & Hlmax)=>{IHl Hl}.
        destruct (IHr _ _ Hr) as (Hrt & Hrmin & Hrmax)=>{IHr Hr}.
        repeat constructor; try done.
        { clear -Hmin Hlmin Hrmin. destruct min as [bot|]; simpl in *; auto.
          apply bool_decide_unpack in Hmin.
          move=>k' Hk'. inversion_clear Hk' as [????? Heq|????? HIn|????? HIn].
          - by rewrite Heq.
          - exact: Hlmin.
          - specialize (Hrmin _ HIn). by etrans. }
        { clear -Hmax Hlmax Hrmax. destruct max as [top|]; simpl in *; auto.
          apply bool_decide_unpack in Hmax.
          move=>k' Hk'. inversion_clear Hk' as [????? Heq|????? HIn|????? HIn].
          - by rewrite Heq.
          - specialize (Hlmax _ HIn). by etrans.
          - exact: Hrmax. }
      Qed.

      Lemma check_canon_ok t : check_canon None None t -> Map.Raw.bst t.
      Proof. move/check_canonP. tauto. Qed.

      Definition build (t : Map.Raw.t A) (pf : check_canon None None t) : Map.t A :=
        {| Map.this := t; Map.is_bst := check_canon_ok _ pf |}.

      Definition from_raw_or (t : Map.Raw.tree A) (default : unit -> Map.t A) : Map.t A :=
        match check_canon None None t as pf
          return (pf -> Map.Raw.bst t) -> Map.t A
        with
        | true => fun pf => {| Map.this := t; Map.is_bst := pf I |}
        | false => fun _ => default()
        end (check_canon_ok t).
      Definition from_raw (t : Map.Raw.tree A) : Map.t A :=
        from_raw_or t $ fun _ =>
        Map.Raw.fold (fun k v acc => Map.add k v acc) t (Map.empty A).

      Definition map_canon (b : Map.t A) : Map.t A :=
        from_raw_or b.(Map.this) $ fun _ => b.

    End canon.

  End MIXIN.

  Module Type MIXIN_LEIBNIZ
      (Key : OrderedType) (Import EqL : LEIBNIZ_EQ Key)
      (Map : MAP Key)
      (Import Extra : MIXIN Key Map).

    #[local] Notation K := Key.t.

    (* This proof requires that [Key.eq a b -> a = b]
       This could be relaxed if we change the statement to:
       [[
       m !! k = Some v -> exists xs ys k',
            map_to_list m = xs ++ (k', v) :: ys /\
            Key.eq k k'
       ]]
     *)
    Lemma map_to_list_elements {A} (k : Key.t) (v : A) (m : Map.t A) :
      m !! k = Some v ->
      exists xs ys, map_to_list m = xs ++ (k, v) :: ys.
    Proof.
      rewrite /lookup/map_to_list/map_fold/map_mapfold.
      rewrite Map.fold_1 fold_left_cons app_nil_r.
      move => H.
      apply Map.find_2 in H.
      apply Map.elements_1 in H.
      eapply InA_alt in H.
      destruct H as [p [H1 H2]].
      rewrite /Map.eq_key_elt/= in H1.
      destruct H1 as [H1 ?]; apply eqL in H1; subst.
      eapply in_split in H2.
      destruct H2 as [l1 [l2 ->]].
      exists (rev l2), (rev l1).
      rewrite rev_app_distr /= -app_assoc. by destruct p.
    Qed.

    Definition find_any {T} (p : K -> T -> bool) (m : Map.t T) : bool :=
      Map.fold (fun k v (acc : bool) => if acc then true else p k v) m false.

    (* This proof only requires that [b] is invariant under [Key.eq], i.e.
       [forall k k' v, Key.eq k k' -> b k v = b k' v]
     *)
    Lemma find_any_ok {T} b (m : Map.t T) :
      if find_any b m
      then exists k v, Map.MapsTo k v m /\ b k v = true
      else forall k v, Map.MapsTo k v m -> b k v = false.
    Proof.
      unfold find_any. rewrite Map.fold_1.
      assert (
        Hsuff :
        if fold_left (λ (a : bool) (p : Map.key * T), if a then true else b p.1 p.2) (Map.elements m) false
        then exists k v, InA (Map.eq_key_elt (elt:=T)) (k, v) (Map.elements m) /\ b k v = true
        else forall k v, InA (Map.eq_key_elt (elt:=T)) (k, v) (Map.elements m) -> b k v = false
      ).
      { rewrite/Map.eq_key_elt.  (* rewrite eqL. /=. *) induction (Map.elements m) as [|kv kvs IH]; simpl.
        { inversion 1. }
        { destruct (b kv.1 kv.2) eqn:?.
          { enough (fold_left (λ (a : bool) (p : Map.key * T), if a then true else b p.1 p.2) kvs true = true) as ->.
            { do 2 eexists. split; eauto. left. split; eauto. reflexivity. }
            clear. induction kvs; simpl; auto. }
          { case_match.
            { destruct IH as (? & ? & ? & ?). do 2 eexists; split; eauto. }
            { inversion 1 as [???Hhd|].
              { cbn in Hhd. destruct Hhd. subst. apply eqL in H3. by subst. }
              { simplify_eq. auto. } } } } }
      { destruct (fold_left _ _ false).
        { destruct Hsuff as [ k [ v [ ? ? ] ] ].
          do 2 eexists. split; eauto using Map.elements_2. }
        { intros. apply Hsuff. eauto using Map.elements_1. } }
    Qed.

  End MIXIN_LEIBNIZ.

End FMapExtra.

(* backwards compatibility *)

Module IM.
  Lemma eqL : forall a b, OT_bs.eq a b -> a = b.
  Proof. done. Qed.
  Include FMapAVL.Make OT_bs.
  Include FMapExtra.MIXIN OT_bs.
  Include FMapExtra.MIXIN_LEIBNIZ OT_bs.
End IM.

#[deprecated(since="20240404", note="use [IM.raw_lookup].")]
Notation IMR_lookup := IM.raw_lookup (only parsing).

#[deprecated(since="20240404", note="use [IM.raw_empty].")]
Notation IMR_empty := IM.raw_empty (only parsing).

#[deprecated(since="20240404", note="use [IM.raw_insert].")]
Notation IMR_insert := IM.raw_insert (only parsing).

#[deprecated(since="20240404", note="use [IM.raw_map].")]
Notation IMR_map := IM.raw_map (only parsing).

#[deprecated(since="20240404", note="use [IM.raw_merge].")]
Notation IMR_merge := IM.raw_merge (only parsing).

#[deprecated(since="20240404", note="use [IM.raw_mapfold].")]
Notation IMR_mapfold := IM.raw_mapfold (only parsing).

#[deprecated(since="20240404", note="use [IM.raw_singleton].")]
Notation IMR_singleton := IM.raw_singleton (only parsing).

#[deprecated(since="20240404", note="use [IM.raw_delete].")]
Notation IMR_delete := IM.raw_delete (only parsing).

#[deprecated(since="20240404", note="use [IM.raw_omap].")]
Notation IMR_omap := IM.raw_omap (only parsing).

#[deprecated(since="20240404", note="use [IM.map_lookup].")]
Notation IM_lookup := IM.map_lookup (only parsing).

#[deprecated(since="20240404", note="use [IM.map_empty].")]
Notation IM_empty := IM.map_empty (only parsing).

#[deprecated(since="20240404", note="use [IM.map_insert].")]
Notation IM_insert := IM.map_insert (only parsing).

#[deprecated(since="20240404", note="use [IM.map_map].")]
Notation IM_map := IM.map_map (only parsing).

#[deprecated(since="20240404", note="use [IM.map_merge].")]
Notation IM_merge := IM.map_merge (only parsing).

#[deprecated(since="20240404", note="use [IM.map_mapfold].")]
Notation IM_mapfold := IM.map_mapfold (only parsing).

#[deprecated(since="20240404", note="use [IM.map_singleton].")]
Notation IM_singleton := IM.map_singleton (only parsing).

#[deprecated(since="20240404", note="use [IM.map_delete].")]
Notation IM_delete := IM.map_delete (only parsing).

#[deprecated(since="20240404", note="use [IM.map_partial_alter].")]
Notation IM_partial_alter := IM.map_partial_alter (only parsing).

#[deprecated(since="20240404", note="use [IM.find_any].")]
Notation find_any := IM.find_any (only parsing).

#[deprecated(since="20240404", note="use [IM.find_any_ok].")]
Notation find_any_ok := IM.find_any_ok (only parsing).

#[deprecated(since="20240404", note="use [IM.check_canon].")]
Notation check_canon := IM.check_canon (only parsing).

#[deprecated(since="20240404", note="use [IM.check_canonP].")]
Notation check_canon_lem := IM.check_canonP (only parsing).

#[deprecated(since="20240404", note="use [IM.check_canon_ok].")]
Notation check_canon_ok := IM.check_canon_ok (only parsing).

#[deprecated(since="20240404", note="use [IM.build].")]
Notation build := IM.build (only parsing).

#[deprecated(since="20240404", note="use [IM.from_raw_or].")]
Notation from_raw_or := IM.from_raw_or (only parsing).

#[deprecated(since="20240404", note="use [IM.from_raw].")]
Notation from_raw := IM.from_raw (only parsing).

#[deprecated(since="20240404", note="use [IM.map_canon].")]
Notation map_canon := IM.map_canon (only parsing).

#[deprecated(since="20240404", note="use [IM.map_to_list_elements].")]
Notation map_to_list_elements := IM.map_to_list_elements (only parsing).
