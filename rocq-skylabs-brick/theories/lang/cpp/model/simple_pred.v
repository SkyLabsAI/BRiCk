(*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import iris.base_logic.lib.own.
Require Import skylabs.iris.extra.base_logic.iprop_own.
Require Import iris.algebra.excl.
Require Import iris.algebra.gmap.
Require Import iris.algebra.lib.frac_auth.
Require Import iris.bi.monpred.
Require Import iris.bi.lib.fractional.
Require Import skylabs.iris.extra.proofmode.proofmode.

Require Import skylabs.iris.extra.bi.fractional.
Require Import skylabs.iris.extra.bi.cancelable_invariants.
Require Import skylabs.lang.cpp.bi.cfractional.
Require Import skylabs.iris.extra.base_logic.own_instances.

Require Import skylabs.prelude.base.
Require Import skylabs.prelude.numbers.
Require Import skylabs.prelude.option.
Require Import skylabs.prelude.arith.z_to_bytes.
Require Import skylabs.lang.cpp.algebra.cfrac.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.lang.cpp.logic.mpred.
Require Import skylabs.lang.cpp.logic.pred.

#[local] Set Printing Coercions.

Implicit Types (vt : validity_type) (σ resolve : genv) (q : cQp.t).

(* todo: does this not exist as a library somewhere? *)
Definition cfractionalR (V : Type) : cmra :=
  prodR cQp.tR (agreeR (leibnizO V)).
Definition cfrac {V : Type} q (v : V) : cfractionalR V :=
  (q, to_agree v).

Lemma cfrac_op {V} (l : V) q1 q2 :
  cfrac q1 l ⋅ cfrac q2 l ≡ cfrac (q1 ⋅ q2) l.
Proof. by rewrite -pair_op agree_idemp. Qed.

Lemma cfrac_valid {A : Type} {q1 q2} {v1 v2 : A} :
  ✓ (cfrac q1 v1 ⋅ cfrac q2 v2) → ✓ (q1 ⋅ q2)%Qp ∧ v1 = v2.
Proof. by move /pair_valid => /= []? /to_agree_op_inv_L. Qed.

Section fractional.
  Context {K V : Type} `{Countable K} `{!HasOwn PROP (gmapR K (cfractionalR V))}.

  Let gmap_own γ q k v :=
    own (A := gmapR K (cfractionalR V)) γ {[ k := cfrac q v ]}.
  #[global] Instance cfractional_own_frac γ k v :
    CFractional (λ q, gmap_own γ q k v).
  Proof. intros q1 q2. by rewrite -own_op singleton_op cfrac_op. Qed.

  #[global] Instance fractional_own_frac_as_fractional γ k v q :
    AsCFractional (gmap_own γ q k v) (λ q, gmap_own γ q k v) q.
  Proof. solve_as_cfrac. Qed.

  #[global] Instance gmap_own_agree
    `{!Sbi PROP} `{!HasOwnValid PROP (gmapR K (cfractionalR V))}
    v1 v2 γ q1 q2 k :
    Observe2 [| v1 = v2 |] (gmap_own γ q1 k v1) (gmap_own γ q2 k v2).
  Proof.
    apply: observe_2_intro_only_provable.
    apply bi.wand_intro_r; rewrite /gmap_own -own_op singleton_op.
    rewrite own_valid internal_cmra_valid_discrete singleton_valid.
    by iIntros "!%" => /cfrac_valid [].
  Qed.

  (**
  We keep this instance local because guarding it with [CFracValid2]
  prevents it from firing. (Perhaps due to the let binding.)
  *)
  Instance gmap_own_cfrac_valid γ
    `{!Sbi PROP} `{!HasOwnValid PROP (gmapR K (cfractionalR V))} :
    ∀ q k v, Observe [| cQp.frac q ≤ 1 |]%Qp (gmap_own γ q k v).
  Proof.
    intros. apply: observe_intro_only_provable.
    rewrite /gmap_own own_valid !internal_cmra_valid_discrete singleton_valid.
    by iIntros "!%" => /pair_valid [? _].
  Qed.
End fractional.
#[local] Existing Instance gmap_own_cfrac_valid.

(** A common valid upper bound determines the value of an owned cell,
    including alternative descriptions whose fractions cannot be combined. *)
Module CFracAgreement.
  Set Default Proof Using "Type*".
  Lemma cfrac_value_included {V : Type} (q : cQp.t) (v : V) (a : cfractionalR V) :
    ✓ a -> Some (cfrac q v) ≼ Some a -> @to_agree (leibnizO V) v ≡ a.2.
  Proof.
    intros Ha Hi. apply Some_included in Hi as [Heq | Hi].
    - exact (proj2 Heq).
    - apply prod_included in Hi as [_ Hi].
      apply agree_valid_included; last exact Hi.
      exact (proj2 Ha).
  Qed.

  Lemma cfrac_map_common_value {K V : Type} `{Countable K}
      (m : gmap K (cfractionalR V)) (k : K) (q1 q2 : cQp.t) (v1 v2 : V) :
    ✓ m -> {[ k := cfrac q1 v1 ]} ≼ m -> {[ k := cfrac q2 v2 ]} ≼ m -> v1 = v2.
  Proof.
    intros Hm H1 H2.
    apply singleton_included_l in H1 as [a [Ha H1]].
    apply singleton_included_l in H2 as [b [Hb H2]].
    have Hab : a ≡ b by apply (inj Some); rewrite <- Ha, <- Hb.
    have Hva : ✓ a. { have Hvalid := Hm k. move: Hvalid. by rewrite Ha. }
    have Hvb : ✓ b. { have Hvalid := Hm k. move: Hvalid. by rewrite Hb. }
    apply (inj (@to_agree (leibnizO V))).
    etrans; first exact (cfrac_value_included _ _ _ Hva H1).
    etrans; first exact (proj2 Hab).
    symmetry. exact (cfrac_value_included _ _ _ Hvb H2).
  Qed.

  Section ownership.
    Context {K V : Type} `{Countable K} `{!inG Σ (gmapR K (cfractionalR V))}.
    Lemma cfrac_own_and_agree (γ : gname) (k : K) (q1 q2 : cQp.t) (v1 v2 : V) :
      iris.base_logic.lib.own.own γ {[ k := cfrac q1 v1 ]} ∧
      iris.base_logic.lib.own.own γ {[ k := cfrac q2 v2 ]} ⊢ ⌜v1 = v2⌝.
    Proof.
      iIntros "H". iDestruct (own_and_total with "H") as (m) "[Hm [%H1 %H2]]".
      iDestruct (iris.base_logic.lib.own.own_valid with "Hm") as %Hm.
      iPureIntro. exact (cfrac_map_common_value m k q1 q2 v1 v2 Hm H1 H2).
    Qed.
  End ownership.

  Section monpred_ownership.
    Context {I : biIndex} {Σ : gFunctors} {K V : Type} `{Countable K}
      `{!inG Σ (gmapR K (cfractionalR V))}.
    Lemma cfrac_mpred_own_and_agree (γ : gname) (k : K) (q1 q2 : cQp.t) (v1 v2 : V) :
      <absorb> (@own (@mpredI I Σ) (gmapR K (cfractionalR V)) _ γ {[ k := cfrac q1 v1 ]}) ∧
      <absorb> (@own (@mpredI I Σ) (gmapR K (cfractionalR V)) _ γ {[ k := cfrac q2 v2 ]}) ⊢ ⌜v1 = v2⌝.
    Proof.
      rewrite /own has_own_monpred_eq /has_own_monpred_def /= has_own_iprop_eq /has_own_iprop_def /=.
      constructor=>i. rewrite !monPred_at_and !monPred_at_absorbingly !monPred_at_embed monPred_at_pure.
      rewrite !bi.absorbing_absorbingly. apply cfrac_own_and_agree.
    Qed.
  End monpred_ownership.

  Section list_agreement.
    Context {PROP : bi} {A : Type}.
    Lemma big_sepL_and_agree (xs ys : list A) (P Q : nat -> A -> PROP) :
      length xs = length ys ->
      (forall i x y, <absorb> P i x ∧ <absorb> Q i y ⊢ ⌜x = y⌝) ->
      <absorb> ([∗ list] i ↦ x ∈ xs, P i x) ∧
      <absorb> ([∗ list] i ↦ y ∈ ys, Q i y) ⊢ ⌜xs = ys⌝.
    Proof.
      revert P Q ys. induction xs as [|x xs IH]; intros P Q [|y ys] Hlen Hagree;
        cbn in Hlen; try discriminate.
      - iIntros "_". done.
      - rewrite !big_sepL_cons !bi.absorbingly_sep !bi.sep_and.
        iIntros "H".
        iAssert (⌜x = y⌝)%I as %->.
        { iApply (Hagree 0 x y). iSplit.
          - iDestruct "H" as "[[H _] _]". iExact "H".
          - iDestruct "H" as "[_ [H _]]". iExact "H". }
        have Htail := IH (fun i => P (S i)) (fun i => Q (S i)) ys
          ltac:(lia) (fun i => Hagree (S i)).
        iDestruct (Htail with "[H]") as %->.
        { iSplit.
          - iDestruct "H" as "[[_ H] _]". iExact "H".
          - iDestruct "H" as "[_ [_ H]]". iExact "H". }
        done.
    Qed.
  End list_agreement.
End CFracAgreement.

Require Import skylabs.lang.cpp.model.inductive_pointers.
(* Stand-in for actual models.
Ensures that everything needed is properly functorized. *)
Import PTRS_IMPL.
Declare Module Import VALUES_DEFS_IMPL : VALUES_INTF_FUNCTOR PTRS_IMPL.

Implicit Types (p : ptr).

Module BaseLayoutChecks.
Definition valid_alignment (sz al : N) : Prop :=
  al = (2 ^ N.log2 al)%N /\ (sz mod al = 0)%N.

#[local] Instance valid_alignment_decision (sz al : N) :
  Decision (valid_alignment sz al).
Proof. unfold valid_alignment. solve_decision. Defined.

(** Sufficient metadata for projecting complete-object pointer typing to a base.
    This concerns pointer extent and alignment, not ownership of base bytes. *)
Definition base_layout_compatible (σ : genv) (derived base : name) : Prop :=
  exists dsz bsz dal bal z,
    size_of σ (Tnamed derived) = Some dsz /\
    size_of σ (Tnamed base) = Some bsz /\
    @align_of σ (Tnamed derived) = Some dal /\
    @align_of σ (Tnamed base) = Some bal /\
    parent_offset σ derived base = Some z /\
    (bal | dal)%N /\ (Z.of_N bal | z)%Z /\
    (0 <= z)%Z /\ (z = 0 \/ z < Z.of_N dsz)%Z /\
    (z + Z.of_N bsz <= Z.of_N dsz)%Z.

Definition tu_base_layout_compatible (tu : translation_unit) (derived base : name) : bool :=
  match tu.(types) !! derived, tu.(types) !! base, parent_offset_tu tu derived base with
  | Some (Gstruct ds), Some (Gstruct bs), Some z =>
      bool_decide (
        valid_alignment ds.(s_size) ds.(s_alignment) /\
        valid_alignment bs.(s_size) bs.(s_alignment) /\
        (bs.(s_alignment) | ds.(s_alignment))%N /\
        (Z.of_N bs.(s_alignment) | z)%Z /\
        (0 <= z)%Z /\ (z = 0 \/ z < Z.of_N ds.(s_size))%Z /\
        (z + Z.of_N bs.(s_size) <= Z.of_N ds.(s_size))%Z)
  | _, _, _ => false
  end.

Lemma tu_base_layout_compatible_sound {σ tu} {Hσ : tu ⊧ σ} derived base :
  tu_base_layout_compatible tu derived base = true ->
  base_layout_compatible σ derived base.
Proof.
  rewrite /tu_base_layout_compatible.
  destruct (tu.(types) !! derived) as [gd|] eqn:Hd; last discriminate.
  destruct gd as [| |ds| | | |]; try discriminate.
  destruct (tu.(types) !! base) as [gb|] eqn:Hb; last discriminate.
  destruct gb as [| |bs| | | |]; try discriminate.
  destruct (parent_offset_tu tu derived base) as [z|] eqn:Hz; last discriminate.
  intros Hcheck. apply bool_decide_eq_true in Hcheck.
  destruct Hcheck as (Hda & Hba & Hdiv & Hdz & Hnonneg & Hstrict & Hbound).
  exists ds.(s_size), bs.(s_size), ds.(s_alignment), bs.(s_alignment), z.
  repeat split; try assumption.
  - exact (size_of_genv_compat tu σ derived ds Hσ Hd).
  - exact (size_of_genv_compat tu σ base bs Hσ Hb).
  - exact (align_of_genv_compat tu derived ds Hσ Hd Hda).
  - exact (align_of_genv_compat tu base bs Hσ Hb Hba).
  - exact (parent_offset_genv_compat Hz).
Qed.

End BaseLayoutChecks.
Import BaseLayoutChecks.

(** A consistency proof for [CPP_LOGIC_CLASS] *)
Module SimpleCPP_BASE <: CPP_LOGIC_CLASS.

  (** Storage identity retains allocation provenance and the stored byte offset.
      Defined aliases share a cell; undefined pointers keep structural keys. *)
  #[local] Existing Instance PTRS_IMPL.root_ptr_eq_dec.
  Definition storage_location : Set := ((root_ptr * Z) + ptr)%type.
  #[global] Instance storage_location_eq_dec : EqDecision storage_location := _.
  #[global] Instance storage_location_countable : Countable storage_location := _.

  Definition storage_key (p : ptr) : storage_location :=
    match p with
    | invalid_ptr_ => inr p
    | offset_ptr root off =>
        match eval_raw_offset (`off) with
        | Some z => inl (root,z)
        | None => inr p
        end
    end.

  Lemma storage_key_offset σ root off z :
    eval_offset σ off = Some z -> storage_key (offset_ptr root off) = inl (root,z).
  Proof. intros Hz. by rewrite /storage_key /eval_offset in Hz |- *; rewrite Hz. Qed.

  Lemma storage_key_cong σ p1 p2 :
    ptr_offset_defined p1 -> ptr_cong σ p1 p2 -> storage_key p1 = storage_key p2.
  Proof.
    intros Hdef (p & o1 & o2 & -> & -> & Hcong).
    apply (ptr_offset_defined_dot σ) in Hdef as [Hp _].
    apply same_property_iff in Hcong as (z & E1 & E2).
    destruct p as [|root off]; first contradiction.
    destruct Hp as [z0 E0].
    have H1 := eval_offset_dot σ off o1 z0 z E0 E1.
    have H2 := eval_offset_dot σ off o2 z0 z E0 E2.
    rewrite _dot.unlock /DOT_dot /= in H1, H2.
    rewrite _dot.unlock /DOT_dot.
    by rewrite (storage_key_offset σ _ _ _ H1) (storage_key_offset σ _ _ _ H2).
  Qed.

  Definition addr : Set := N.
  Definition byte : Set := N.
  Variant runtime_val' : Set :=
  | Rundef
    (* ^ undefined value, semantically, it means "any value" *)
  | Rval (_ : byte)
    (* ^ machine level byte *)
  | Rpointer_chunk (_ : ptr) (index : nat).
    (* ^ you need the same pointer and consecutive integers to "have" a pointer.
     *)

  Definition Z_to_bytes {σ:genv} (n : bitsize) (sgn: signed) (v : Z) : list runtime_val' :=
    Rval <$> _Z_to_bytes (bitsize.bytesNat n) (genv_byte_order σ) sgn v.

  Lemma length_Z_to_bytes {σ} n sgn v : length (Z_to_bytes n sgn v) = bitsize.bytesNat n.
  Proof. by rewrite /Z_to_bytes length_fmap _Z_to_bytes_length. Qed.

  Record cpp_ghost' : Type :=
    { heap_name : gname
    ; ghost_mem_name : gname
    ; mem_inj_name : gname
    ; blocks_name : gname
    ; code_name : gname
    ; derivations_name : gname
    }.
  Definition _cpp_ghost := cpp_ghost'.

  Record cppG' (Σ : gFunctors) : Type :=
    { heapGS : inG Σ (gmapR addr (cfractionalR runtime_val'))
      (* ^ this represents the contents of physical memory *)
    ; ghost_memG : inG Σ (gmapR storage_location (cfractionalR val))
      (* ^ this represents the contents of the C++ runtime that might
         not be represented in physical memory, e.g. values stored in
         registers or temporaries on the stack *)
    ; mem_injG : inG Σ (gmapUR storage_location (agreeR (leibnizO (option addr))))
      (* ^ this carries the (compiler-supplied) mapping from C++ storage
         locations to physical memory addresses. Defined congruent aliases use
         the same location key, including for ghost-backed cells. Locations that
         are not stored in physical memory (e.g. because they are register
         allocated) are mapped to [None] *)
    ; blocksG : inG Σ (gmapUR ptr (agreeR (leibnizO (Z * Z))))
      (* ^ this represents the minimum and maximum offset of the block *)
    ; codeG : inG Σ (gmapUR ptr (agreeR (leibnizO (Func + Method + Ctor + Dtor))))
      (* ^ this carries the (compiler-supplied) mapping from C++ locations
         to the code stored at that location *)
    ; derivationsG : inG Σ (gmapUR ptr (cfractionalR (leibnizO (globname * list globname))))
    ; has_inv' : invGS Σ
    ; has_brG' : br.ghost.G Σ
    }.

  Definition cppPreG : gFunctors -> Type := cppG'.

  Definition has_inv Σ : cppPreG Σ -> invGS Σ := @has_inv' Σ.
  Definition has_brG Σ : cppPreG Σ -> br.ghost.G Σ := @has_brG' Σ.

  Include CPP_LOGIC_CLASS_MIXIN.

  Section with_cpp.
    Context `{!cpp_logic thread_info Σ}.

    Existing Class cppG'.
    #[local] Instance cppPreG_cppG' : cppG' Σ := cpp_has_cppG.
    #[local] Existing Instances heapGS ghost_memG mem_injG blocksG codeG derivationsG.

    Definition heap_own (a : addr) q (r : runtime_val') : mpred :=
      own (A := gmapR addr (cfractionalR runtime_val'))
        cpp_ghost.(heap_name) {[ a := cfrac q r ]}.
    Definition ghost_mem_own (p : ptr) q (v : val) : mpred :=
      own (A := gmapR storage_location (cfractionalR val))
        cpp_ghost.(ghost_mem_name) {[ storage_key p := cfrac q v ]}.
    Definition mem_inj_own (p : ptr) (va : option N) : mpred :=
      own (A := gmapUR storage_location (agreeR (leibnizO (option addr))))
        cpp_ghost.(mem_inj_name) {[ storage_key p := to_agree va ]}.
    Definition blocks_own (p : ptr) (l h : Z) : mpred :=
      own (A := gmapUR ptr (agreeR (leibnizO (Z * Z))))
        cpp_ghost.(blocks_name) {[ p := to_agree (l, h) ]}.
    Lemma blocks_own_range_agree p l1 h1 l2 h2 :
      blocks_own p l1 h1 ∗ blocks_own p l2 h2 ⊢ ⌜(l1,h1) = (l2,h2)⌝.
    Proof.
      rewrite /blocks_own -own_op singleton_op.
      rewrite own_valid internal_cmra_valid_discrete singleton_valid.
      by iIntros "!%" => /= /to_agree_op_inv_L.
    Qed.

    Definition _code_own (p : ptr) (f : Func + Method + Ctor + Dtor) : mpred :=
      own cpp_ghost.(code_name)
        (A := gmapUR ptr (agreeR (leibnizO (Func + Method + Ctor + Dtor))))
        {[ p := to_agree f ]}.
    Definition derivation_own (p : ptr) q (l : globname) (mdc : list globname) : mpred :=
      own (A := gmapUR ptr (cfractionalR (leibnizO (globname * list globname))))
        cpp_ghost.(derivations_name) {[ p := cfrac q (l, mdc) ]}.

    #[global] Instance mem_inj_own_persistent p va : Persistent (mem_inj_own p va) := _.
    #[global] Instance mem_inj_own_affine p va : Affine (mem_inj_own p va) := _.
    #[global] Instance mem_inj_own_timeless p va : Timeless (mem_inj_own p va) := _.

    #[global] Instance _code_own_persistent p f : Persistent (_code_own p f) := _.
    #[global] Instance _code_own_affine p f : Affine (_code_own p f) := _.
    #[global] Instance _code_own_timeless p f : Timeless (_code_own p f) := _.
  End with_cpp.
  #[global] Typeclasses Opaque mem_inj_own _code_own.
End SimpleCPP_BASE.

(* TODO: provide an instance for this. *)
Module Type SimpleCPP_VIRTUAL.
  Import SimpleCPP_BASE.

  Parameter vbyte : forall `{!cpp_logic thread_info Σ}
    (va : addr) (rv : runtime_val') (q : Qp), mpred.
  Section with_cpp.
    Context `{cpp_logic}.

    Axiom vbyte_fractional : forall va rv, Fractional (vbyte va rv).
    Axiom vbyte_timeless : forall va rv q, Timeless (vbyte va rv q).
    #[global] Existing Instances vbyte_fractional vbyte_timeless.

    Definition vbytes (a : addr) (rv : list runtime_val') (q : Qp) : mpred :=
      [∗list] o ↦ v ∈ rv, (vbyte (a+N.of_nat o)%N v q).

    #[global] Instance vbytes_fractional va rv : Fractional (vbytes va rv).
    Proof. apply fractional_big_sepL; intros. apply vbyte_fractional. Qed.

    #[global] Instance vbytes_as_fractional va rv q :
      AsFractional (vbytes va rv q) (vbytes va rv) q.
    Proof. exact: Build_AsFractional. Qed.

    #[global] Instance vbytes_timeless va rv q : Timeless (vbytes va rv q) := _.
  End with_cpp.
End SimpleCPP_VIRTUAL.

Module SimpleCPP.
  Include SimpleCPP_BASE.
  Include SimpleCPP_VIRTUAL.

  Definition runtime_val := runtime_val'.

  Parameter live_alloc_id : forall `{!cpp_logic thread_info Σ}, alloc_id -> mpred.

  Section with_cpp.
    Context `{cpp_logic} {σ}.

    Axiom live_alloc_id_timeless : forall aid, Timeless (live_alloc_id aid).
    #[global] Existing Instance live_alloc_id_timeless.

    Definition live_ptr (p : ptr) :=
      default False%I (live_alloc_id <$> ptr_alloc_id p).
    Axiom nullptr_live : |-- live_ptr nullptr.
    Typeclasses Opaque live_ptr.

    (** pointer validity *)
    (** Pointers past the end of an object/array can be valid; see
    https://eel.is/c++draft/expr.add#4 *)
    Definition in_range (vt : validity_type) (l o h : Z) : mpred :=
      [| (l <= o < h)%Z \/ (vt = Relaxed /\ o = h) |].

    Lemma in_range_weaken l o h :
      in_range Strict l o h |-- in_range Relaxed l o h.
    Proof. rewrite /in_range/=. f_equiv. rewrite/impl. tauto. Qed.

    (** Check every stored path prefix against the same allocation range. Only
        the final endpoint may use relaxed validity at the upper bound; every
        proper prefix must be strictly inside the range.
        Addresses are computed by the pointer model's existing fold. *)
    Import inductive_pointers_utils.address_sums.
    Definition raw_path_valid (vt : validity_type) (root : root_ptr)
        (l h : Z) (path : raw_offset) : Prop :=
      forall prefix suffix, path = prefix ++ suffix ->
        exists z va,
          eval_raw_offset prefix = Some z /\
          foldr (fun off ova => ova ≫= offset_vaddr off)
            (root_ptr_vaddr root) (snd <$> prefix) = Some va /\
          va <> 0%N /\
          ((l <= z < h)%Z \/ (suffix = [] /\ vt = Relaxed /\ z = h)).

    Lemma raw_path_valid_prefix vt root l h prefix suffix :
      raw_path_valid vt root l h (prefix ++ suffix) ->
      raw_path_valid vt root l h prefix.
    Proof.
      intros Hpath before after E.
      have Hsplit : prefix ++ suffix = before ++ (after ++ suffix) by rewrite E app_assoc.
      destruct (Hpath before (after ++ suffix) Hsplit)
        as (z & va & Hz & Hva & Hnz & Hr).
      exists z, va. repeat split; try assumption.
      destruct Hr as [Hr|[Htail [Hvt Hend]]]; first by left.
      apply app_eq_nil in Htail as [Hafter _]. naive_solver.
    Qed.

    Lemma raw_path_valid_strict_prefix vt root l h prefix suffix :
      suffix <> [] ->
      raw_path_valid vt root l h (prefix ++ suffix) ->
      raw_path_valid Strict root l h prefix.
    Proof.
      intros Hsuffix Hpath before after E.
      have Hsplit : prefix ++ suffix = before ++ (after ++ suffix) by rewrite E app_assoc.
      destruct (Hpath before (after ++ suffix) Hsplit)
        as (z & va & Hz & Hva & Hnz & Hr).
      exists z, va. repeat split; try assumption.
      destruct Hr as [Hr|[Htail _]]; first by left.
      apply app_eq_nil in Htail as [_ Htail]. contradiction.
    Qed.

    Lemma raw_path_valid_weaken root l h path :
      raw_path_valid Strict root l h path -> raw_path_valid Relaxed root l h path.
    Proof.
      intros Hpath prefix suffix E.
      destruct (Hpath prefix suffix E) as (z & va & Hz & Hva & Hnz & Hr).
      exists z, va. repeat split; try assumption. destruct Hr as [Hr|[_ [Hbad _]]];
        [by left|discriminate].
    Qed.

    Lemma raw_path_valid_nil vt root l h va :
      root_ptr_vaddr root = Some va -> va <> 0%N ->
      ((l <= 0 < h)%Z \/ (vt = Relaxed /\ 0%Z = h)) ->
      raw_path_valid vt root l h [].
    Proof.
      intros Hva Hnz Hr prefix suffix E.
      symmetry in E. apply app_eq_nil in E as [-> ->].
      exists 0%Z, va. repeat split; try assumption; naive_solver.
    Qed.

    Lemma raw_path_valid_snoc vt root l h path seg z va :
      raw_path_valid Strict root l h path ->
      eval_raw_offset (path ++ [seg]) = Some z ->
      foldr (fun off ova => ova ≫= offset_vaddr off)
        (root_ptr_vaddr root) (snd <$> (path ++ [seg])) = Some va ->
      va <> 0%N -> ((l <= z < h)%Z \/ (vt = Relaxed /\ z = h)) ->
      raw_path_valid vt root l h (path ++ [seg]).
    Proof.
      intros Hpath Hz Hva Hnz Hr prefix suffix.
      induction suffix as [|last suffix IH] using rev_ind; intros E.
      - rewrite app_nil_r in E. subst prefix. exists z, va.
        repeat split; try assumption; naive_solver.
      - rewrite app_assoc in E. apply app_inj_tail in E as [E _].
        destruct (Hpath prefix suffix E) as (z' & va' & Hz' & Hva' & Hnz' & Hr').
        exists z', va'. repeat split; try assumption; naive_solver.
    Qed.

    Section subscript_interpolation.
      #[local] Open Scope Z_scope.

      Lemma raw_path_valid_end vt root l h path :
        raw_path_valid vt root l h path ->
        exists z va,
          eval_raw_offset path = Some z /\
          foldr (fun off ova => ova ≫= offset_vaddr off)
            (root_ptr_vaddr root) (snd <$> path) = Some va /\
          va <> 0%N /\ ((l <= z < h) \/ (vt = pred.Relaxed /\ z = h)).
      Proof.
        intros Hpath.
        destruct (Hpath path [] (eq_sym (app_nil_r _)))
          as (z & va & Hz & Hva & Hnz & Hr).
        exists z, va. repeat split; try assumption.
        destruct Hr as [Hr|[_ Hr]]; by [left|right].
      Qed.

      Lemma raw_path_valid_subscript_interpolate vt1 vt2 vt root l h
          prefix ty n d (s : N) i j k :
        i <= j < k ->
        (vt = pred.Strict -> (0 < s)%N) ->
        raw_path_valid vt1 root l h
          (prefix ++ raw_offset_collapse [(o_sub_ ty (n+i), d + Z.of_N s * i)]) ->
        raw_path_valid vt2 root l h
          (prefix ++ raw_offset_collapse [(o_sub_ ty (n+k), d + Z.of_N s * k)]) ->
        raw_path_valid vt root l h
          (prefix ++ raw_offset_collapse [(o_sub_ ty (n+j), d + Z.of_N s * j)]).
      Proof.
        intros Hijk Hpositive Hpi Hpk.
        have Hproper x mode :
            n+x <> 0 ->
            raw_path_valid mode root l h
              (prefix ++ raw_offset_collapse [(o_sub_ ty (n+x), d + Z.of_N s * x)]) ->
            raw_path_valid pred.Strict root l h prefix.
        { intros Hnx Hpath.
          apply (raw_path_valid_strict_prefix mode root l h prefix
            (raw_offset_collapse [(o_sub_ ty (n+x), d + Z.of_N s * x)])).
          - rewrite /= /offset_seg_cons decide_False; [discriminate|naive_solver].
          - exact Hpath. }
        have Hpre : raw_path_valid pred.Strict root l h prefix.
        { destruct (decide (n+i=0)) as [E|E].
          - apply (Hproper k vt2); [lia|exact Hpk].
          - exact (Hproper i vt1 E Hpi). }
        destruct (raw_path_valid_end _ _ _ _ _ Hpre)
          as (zp & vp & Ep & Ap & Np & Rp).
        destruct Rp as [Rp|[Hbad _]]; last discriminate.
        destruct (raw_path_valid_end _ _ _ _ _ Hpi)
          as (zi & vi & Ei & Ai & Ni & Ri).
        destruct (raw_path_valid_end _ _ _ _ _ Hpk)
          as (zk & vk & Ek & Ak & Nk & Rk).
        rewrite eval_subscript_collapse Ep in Ei.
        rewrite eval_subscript_collapse Ep in Ek.
        injection Ei as <-. injection Ek as <-.
        have Hdi : d + Z.of_N s * i <= d + Z.of_N s * j by nia.
        have Hdk : d + Z.of_N s * j <= d + Z.of_N s * k by nia.
        rewrite fold_subscript_collapse in Ai.
        destruct (fold_offset_vaddr_increase_tail (snd <$> prefix) (root_ptr_vaddr root)
          (d + Z.of_N s * i) (d + Z.of_N s * j) vi Hdi Ai)
          as (vj & Aj & Ej).
        have Nj : vj <> 0%N by lia.
        have Rj : l <= zp + (d + Z.of_N s * j) < h \/
            (vt = pred.Relaxed /\ zp + (d + Z.of_N s * j) = h).
        { destruct vt.
          - have Hs := Hpositive eq_refl.
            have Hstrict : d + Z.of_N s * j < d + Z.of_N s * k by nia.
            destruct Ri as [Ri|[_ Ri]]; destruct Rk as [Rk|[_ Rk]]; left; lia.
          - destruct (decide (zp + (d + Z.of_N s * j) < h)) as [Hlt|Hlt].
            + left. destruct Ri as [Ri|[_ Ri]]; destruct Rk as [Rk|[_ Rk]]; lia.
            + right. split; first done.
              destruct Ri as [Ri|[_ Ri]]; destruct Rk as [Rk|[_ Rk]]; lia. }
        destruct (decide (n+j=0 /\ d + Z.of_N s * j=0)) as [Hzero|Hnon].
        - have Etail : raw_offset_collapse [(o_sub_ ty (n+j), d + Z.of_N s * j)] = [].
          { by rewrite /= /offset_seg_cons decide_True. }
          rewrite Etail app_nil_r. destruct vt; first exact Hpre.
          exact (raw_path_valid_weaken _ _ _ _ Hpre).
        - have Etail : raw_offset_collapse [(o_sub_ ty (n+j), d + Z.of_N s * j)] =
              [(o_sub_ ty (n+j), d + Z.of_N s * j)].
          { by rewrite /= /offset_seg_cons decide_False. }
          rewrite Etail.
          apply (raw_path_valid_snoc vt root l h prefix _
            (zp + (d + Z.of_N s * j)) vj); try assumption.
          + rewrite eval_raw_offset_app Ep.
            change (liftM2 Z.add (Some zp) (Some (d + Z.of_N s * j + 0)) =
              Some (zp + (d + Z.of_N s * j))).
            by rewrite Z.add_0_r.
          + by rewrite fmap_app foldr_app /=.
      Qed.
      Lemma raw_path_valid_subscript_increase vt root l h prefix ty n d m delta z :
        raw_path_valid pred.Strict root l h
          (prefix ++ raw_offset_collapse [(o_sub_ ty n,d)]) ->
        eval_raw_offset (prefix ++ raw_offset_collapse [(o_sub_ ty n,d)]) = Some z ->
        0 <= delta ->
        (z + delta < h \/ (vt = pred.Relaxed /\ z + delta = h)) ->
        raw_path_valid vt root l h
          (prefix ++ raw_offset_collapse [(o_sub_ ty m,d+delta)]).
      Proof.
        intros Hpath Hz Hdelta Hbound.
        have Hpre := raw_path_valid_prefix _ _ _ _ _ _ Hpath.
        destruct (raw_path_valid_end _ _ _ _ _ Hpre)
          as (zp & vp & Ep & Ap & Np & Rp).
        destruct (raw_path_valid_end _ _ _ _ _ Hpath)
          as (zi & vi & Ei & Ai & Ni & Ri).
        rewrite Hz in Ei. injection Ei as <-.
        rewrite eval_subscript_collapse Ep in Hz. injection Hz as Hz.
        rewrite fold_subscript_collapse in Ai.
        destruct (fold_offset_vaddr_increase_tail (snd <$> prefix) (root_ptr_vaddr root)
          d (d+delta) vi ltac:(lia) Ai) as (vj & Aj & Ej).
        have Nj : vj <> 0%N by lia.
        have Rj : l <= zp + (d+delta) < h \/
            (vt = pred.Relaxed /\ zp + (d+delta) = h).
        { destruct Ri as [Ri|[Hbad _]]; last discriminate.
          destruct Hbound as [Hb|[Hvt Hb]]; [left|right]; split; try assumption; lia. }
        destruct (decide (m=0 /\ d+delta=0)) as [Hzero|Hnon].
        - have Etail : raw_offset_collapse [(o_sub_ ty m,d+delta)] = [].
          { by rewrite /= /offset_seg_cons decide_True. }
          rewrite Etail app_nil_r. destruct vt; first exact Hpre.
          exact (raw_path_valid_weaken _ _ _ _ Hpre).
        - have Etail : raw_offset_collapse [(o_sub_ ty m,d+delta)] =
              [(o_sub_ ty m,d+delta)].
          { by rewrite /= /offset_seg_cons decide_False. }
          rewrite Etail.
          apply (raw_path_valid_snoc vt root l h prefix _ (zp + (d+delta)) vj);
            try assumption.
          + rewrite eval_raw_offset_app Ep.
            change (liftM2 Z.add (Some zp) (Some (d+delta+0)) = Some (zp+(d+delta))).
            by rewrite Z.add_0_r.
          + by rewrite fmap_app foldr_app /=.
      Qed.
    End subscript_interpolation.

    Lemma raw_path_valid_base_increase vt root l h path derived base z0 z :
      raw_offset_collapse path = path ->
      raw_path_valid pred.Strict root l h path ->
      eval_raw_offset path = Some z0 ->
      (0 <= z)%Z ->
      ((z0 + z < h)%Z \/ (vt = pred.Relaxed /\ (z0 + z = h)%Z)) ->
      raw_path_valid vt root l h
        (raw_offset_collapse (path ++ [(o_base_ derived base,z)])).
    Proof.
      intros Hwf Hpath E0 Hz Hb.
      destruct (raw_offset_collapse_base_snoc path derived base z Hwf (ex_intro _ z0 E0))
        as [(prefix & Epre & E)|E]; rewrite E.
      - have Hpre : raw_path_valid pred.Strict root l h prefix.
        { apply (raw_path_valid_prefix pred.Strict root l h prefix
            [(o_derived_ base derived,(-z)%Z)]). by rewrite -Epre. }
        destruct vt; [exact Hpre|by apply raw_path_valid_weaken].
      - destruct (raw_path_valid_end _ _ _ _ _ Hpath)
          as (z' & va0 & Ez & A0 & N0 & R0).
        rewrite E0 in Ez. injection Ez as <-.
        have Azero :
          foldr (fun off ova => ova ≫= offset_vaddr off)
            (root_ptr_vaddr root ≫= offset_vaddr 0) (snd <$> path) = Some va0.
        { destruct root; simpl in *; by rewrite offset_vaddr_0. }
        destruct (fold_offset_vaddr_increase_tail (snd <$> path)
          (root_ptr_vaddr root) 0 z va0 Hz Azero) as (va & Ava & Hsum).
        apply (raw_path_valid_snoc vt root l h path _ (z0+z)%Z va); try done.
        + rewrite eval_raw_offset_app E0 /=.
          change (Some (z0+(z+0))%Z = Some (z0+z)%Z).
          by rewrite Z.add_0_r.
        + by rewrite fmap_app foldr_app /=.
        + lia.
        + destruct R0 as [R0|[Hbad _]]; last discriminate.
          destruct Hb as [Hb|[-> Hb]]; [left; lia|by right].
    Qed.

    Lemma raw_path_valid_vaddr {resolve : genv} vt root l h off :
      raw_path_valid vt root l h (proj1_sig off) ->
      exists va, @ptr_vaddr resolve (offset_ptr root off) = Some va /\ va <> 0%N.
    Proof.
      intros Hpath. destruct (Hpath (proj1_sig off) [] (eq_sym (app_nil_r _)))
        as (z & va & Hz & Hva & Hnz & _).
      exists va. split; last done. by rewrite /ptr_vaddr Hz.
    Qed.

    (** Non-null validity uses a range owned at the canonical allocation root,
        non-null provenance, and prefix validity. Physical storage is separate:
        [mem_inj_own p None] continues to represent ghost cells. *)
    Definition _valid_ptr vt (p : ptr) : mpred :=
      [| p = nullptr /\ vt = Relaxed |] \\//
        match p with
        | invalid_ptr_ => False
        | offset_ptr root off =>
            Exists l h, blocks_own (lift_root_ptr root) l h **
              [| exists aid, root_ptr_alloc_id root = Some aid /\ aid <> null_alloc_id |] **
              [| raw_path_valid vt root l h (proj1_sig off) |]
        end.
    Notation strict_valid_ptr := (_valid_ptr Strict).
    Notation valid_ptr := (_valid_ptr Relaxed).

    Instance _valid_ptr_persistent : forall b p, Persistent (_valid_ptr b p).
    Proof. intros b [|root off]; apply _. Qed.
    Instance _valid_ptr_affine : forall b p, Affine (_valid_ptr b p).
    Proof. intros b [|root off]; apply _. Qed.
    Instance _valid_ptr_timeless : forall b p, Timeless (_valid_ptr b p).
    Proof. intros b [|root off]; apply _. Qed.

    Lemma _valid_ptr_cases {resolve : genv} vt p :
      _valid_ptr vt p |--
      [| p = nullptr \/
         ((exists aid, ptr_alloc_id p = Some aid /\ aid <> null_alloc_id) /\
          (exists va, @ptr_vaddr resolve p = Some va /\ va <> 0%N)) |].
    Proof.
      rewrite /_valid_ptr. iDestruct 1 as "[[% _]|H]"; first by iLeft.
      destruct p as [|root off]; first by iDestruct "H" as %[].
      iDestruct "H" as (l h) "(_ & %Haid & %Hpath)".
      iPureIntro. right. split; first exact Haid.
      exact (raw_path_valid_vaddr _ _ _ _ _ Hpath).
    Qed.

    Lemma same_address_eq_null p tv :
      _valid_ptr tv p |-- [| same_address p nullptr <-> p = nullptr |].
    Proof.
      iIntros "H". iDestruct (_valid_ptr_cases with "H") as %Hchecked.
      iPureIntro. rewrite same_address_eq same_property_iff ptr_vaddr_nullptr.
      destruct Hchecked as [->|[_ (va & Hva & Hnz)]]; first naive_solver.
      split; first naive_solver. intros ->. by exists 0%N.
    Qed.

    Theorem valid_ptr_nullptr : |-- valid_ptr nullptr.
    Proof. by iLeft. Qed.

    Theorem not_strictly_valid_ptr_nullptr : strict_valid_ptr nullptr |-- False.
    Proof.
      rewrite /_valid_ptr. iDestruct 1 as "[[_ %Hvt]|H]"; first discriminate.
      iDestruct "H" as (l h) "(_ & %Haid & _)".
      destruct Haid as (aid & Haid & Hnz). simpl in Haid. naive_solver.
    Qed.
    Typeclasses Opaque _valid_ptr.

    Lemma strict_valid_valid p : strict_valid_ptr p |-- valid_ptr p.
    Proof.
      rewrite /_valid_ptr. iDestruct 1 as "[[_ %Hvt]|H]"; first discriminate.
      iRight. destruct p as [|root off]; first done.
      iDestruct "H" as (l h) "(B & %Haid & %Hpath)".
      iExists l, h. iFrame "B". iSplit; first done.
      iPureIntro. by apply raw_path_valid_weaken.
    Qed.

    Lemma _valid_ptr_alloc_id vt p :
      _valid_ptr vt p |-- [| is_Some (ptr_alloc_id p) |].
    Proof.
      rewrite /_valid_ptr. iDestruct 1 as "[[-> _]|H]".
      - iPureIntro. by exists null_alloc_id.
      - destruct p as [|root off]; first by iDestruct "H" as %[].
        iDestruct "H" as (l h) "(_ & %Haid & _)".
        iPureIntro. destruct Haid as (aid & Haid & _). by exists aid.
    Qed.

    Lemma valid_ptr_alloc_id : forall p,
      valid_ptr p |-- [| is_Some (ptr_alloc_id p) |].
    Proof. intros. apply _valid_ptr_alloc_id. Qed.

    Lemma _valid_ptr_vaddr {resolve : genv} vt p :
      _valid_ptr vt p |-- [| is_Some (@ptr_vaddr resolve p) |].
    Proof.
      iIntros "H". iDestruct (_valid_ptr_cases (resolve:=resolve) with "H") as %Hchecked.
      iPureIntro. destruct Hchecked as [->|[_ (va & Hva & _)]];
        [by exists 0%N|by exists va].
    Qed.

    Lemma _valid_ptr_offset_defined vt p :
      _valid_ptr vt p |-- [| ptr_offset_defined p |].
    Proof.
      rewrite /_valid_ptr. iDestruct 1 as "[[-> _]|H]".
      - iPureIntro. by exists 0%Z.
      - destruct p as [|root off]; first by iDestruct "H" as %[].
        iDestruct "H" as (l h) "(_ & _ & %Hpath)".
        destruct (Hpath (proj1_sig off) [] (eq_sym (app_nil_r _)))
          as (z & va & Hz & _).
        iPureIntro. by exists z.
    Qed.

    Lemma strict_valid_ptr_nonnull_alloc_id p :
      strict_valid_ptr p |--
      [| exists aid, ptr_alloc_id p = Some aid /\ aid <> null_alloc_id |].
    Proof.
      rewrite /_valid_ptr. iDestruct 1 as "[[_ %Hvt]|H]"; first discriminate.
      destruct p as [|root off]; first by iDestruct "H" as %[].
      iDestruct "H" as (l h) "(_ & $ & _)".
    Qed.

    Lemma strict_valid_ptr_off_nonnull p o :
      strict_valid_ptr (p ,, o) |-- [| p <> nullptr |].
    Proof.
      iIntros "H".
      iDestruct (strict_valid_ptr_nonnull_alloc_id with "H") as %(aid & Haid & Hnn).
      iPureIntro. intros ->.
      have Hroot := ptr_alloc_id_offset (p:=nullptr) (o:=o) (ex_intro _ aid Haid).
      rewrite ptr_alloc_id_nullptr Haid in Hroot.
      injection Hroot as ->. contradiction.
    Qed.

    (** This is a very simplistic definition of [provides_storage].
    A more useful definition should probably not be persistent. *)
    Definition provides_storage (storage_ptr obj_ptr : ptr) (_ : type) : mpred :=
      [| same_address storage_ptr obj_ptr |] ** valid_ptr storage_ptr ** valid_ptr obj_ptr.
    #[global] Instance provides_storage_persistent storage_ptr obj_ptr ty :
      Persistent (provides_storage storage_ptr obj_ptr ty) := _.
    #[global] Instance provides_storage_affine storage_ptr obj_ptr ty :
      Affine (provides_storage storage_ptr obj_ptr ty) := _.
    #[global] Instance provides_storage_timeless storage_ptr obj_ptr ty :
      Timeless (provides_storage storage_ptr obj_ptr ty) := _.
    #[global] Instance provides_storage_same_address storage_ptr obj_ptr ty :
      Observe [| same_address storage_ptr obj_ptr |] (provides_storage storage_ptr obj_ptr ty) := _.

    #[global] Instance provides_storage_valid_storage_ptr storage_ptr obj_ptr aty :
      Observe (valid_ptr storage_ptr) (provides_storage storage_ptr obj_ptr aty) := _.
    #[global] Instance provides_storage_valid_obj_ptr storage_ptr obj_ptr aty :
      Observe (valid_ptr obj_ptr) (provides_storage storage_ptr obj_ptr aty) := _.

    Section with_genv.

      Let POINTER_BITSZ : bitsize := pointer_size_bitsize σ.
      Notation POINTER_BYTES := (bitsize.bytesNat POINTER_BITSZ).

      Definition aptr (p : ptr) : list runtime_val :=
        Rpointer_chunk p <$> (seq 0 POINTER_BYTES).

      Definition cptr (a : N) : list runtime_val :=
        Z_to_bytes POINTER_BITSZ Unsigned (Z.of_N a).

      Lemma length_aptr p : length (aptr p) = POINTER_BYTES.
      Proof. by rewrite /aptr length_fmap length_seq. Qed.
      Lemma length_cptr a : length (cptr a) = POINTER_BYTES.
      Proof. by rewrite /cptr length_Z_to_bytes. Qed.

      Lemma bytesNat_pos b : bitsize.bytesNat b > 0.
      Proof. by case: b =>/=; lia. Qed.

      Lemma bytesNat_nnonnull b : bitsize.bytesNat b <> 0.
      Proof. have := bytesNat_pos b. lia. Qed.
      #[local] Hint Resolve bytesNat_nnonnull : core.

      Lemma bytesNat_nnonnull' b : bitsize.bytesNat b = S (pred (bitsize.bytesNat b)).
      Proof. by rewrite (Nat.succ_pred _ (bytesNat_nnonnull _)). Qed.

      Lemma list_not_nil_cons {T} (xs : list T) : xs <> nil -> ∃ h t, xs = h :: t.
      Proof. case: xs => //= x xs. eauto. Qed.

      Lemma _Z_to_bytes_cons n x y z : n <> 0 -> ∃ a b, _Z_to_bytes n x y z = a :: b.
      Proof.
        intros Hne.
        apply list_not_nil_cons.
        rewrite -(Nat.succ_pred n Hne) {Hne} _Z_to_bytes_eq /_Z_to_bytes_def /=.
        case: x => //= Heq.
        eapply app_cons_not_nil, symmetry, Heq.
      Qed.
      Lemma Z_to_bytes_cons bs x y : ∃ a b, Z_to_bytes bs x y = Rval a :: b.
      Proof.
        unfold Z_to_bytes.
        edestruct _Z_to_bytes_cons as (? & ? & ->) => //; eauto.
      Qed.

      Lemma cptr_ne_aptr p n : cptr n <> aptr p.
      Proof.
        rewrite /cptr /aptr bytesNat_nnonnull'.
        by edestruct Z_to_bytes_cons as (? & ? & ->).
      Qed.

      (** WRT pointer equality, see https://eel.is/c++draft/expr.eq#3 *)
      Definition pure_encodes_undef (n : bitsize) (vs : list runtime_val) : Prop :=
        vs = repeat Rundef (bitsize.bytesNat n).
      Lemma length_pure_encodes_undef n vs :
        pure_encodes_undef n vs ->
        length vs = bitsize.bytesNat n.
      Proof. rewrite /pure_encodes_undef => ->. exact: repeat_length. Qed.

      Definition in_Z_to_bytes_bounds (cnt' : bitsize) sgn z :=
        let cnt := bitsize.bytesNat cnt' in
        match sgn with
        | Signed => (- 2 ^ (8 * cnt - 1) ≤ z)%Z ∧ (z ≤ 2 ^ (8 * cnt - 1) - 1)%Z
        | Unsigned => (0 ≤ z)%Z ∧ (z < 2 ^ (8 * cnt))%Z
        end.

      Lemma _Z_to_bytes_inj_1 cnt endianness sgn z :
        in_Z_to_bytes_bounds cnt sgn z ->
        _Z_from_bytes endianness sgn (_Z_to_bytes (bitsize.bytesNat cnt) endianness sgn z) = z.
      Proof. apply _Z_from_to_bytes_roundtrip. Qed.

      Lemma _Z_to_bytes_inj_2 cnt endianness sgn z1 z2 :
        in_Z_to_bytes_bounds cnt sgn z1 ->
        in_Z_to_bytes_bounds cnt sgn z2 ->
        _Z_to_bytes (bitsize.bytesNat cnt) endianness sgn z1 = _Z_to_bytes (bitsize.bytesNat cnt) endianness sgn z2 ->
        z1 = z2.
      Proof.
        intros Hb1 Hb2 Heq%(f_equal (_Z_from_bytes endianness sgn)).
        move: Heq. by rewrite !_Z_to_bytes_inj_1.
      Qed.
      Instance: Inj eq eq Rval.
      Proof. by injection 1. Qed.

      Lemma Z_to_bytes_inj cnt sgn z1 z2 :
        in_Z_to_bytes_bounds cnt sgn z1 ->
        in_Z_to_bytes_bounds cnt sgn z2 ->
        Z_to_bytes cnt sgn z1 = Z_to_bytes cnt sgn z2 ->
        z1 = z2.
      Proof.
        rewrite /Z_to_bytes; intros Hb1 Hb2 Heq%(inj (fmap Rval)).
        exact: _Z_to_bytes_inj_2.
      Qed.

      Definition pure_encodes (t : type) (v : val) (vs : list runtime_val) : Prop :=
        match erase_qualifiers t with
        | Tnum sz sgn =>
          match v with
          | Vint v =>
            in_Z_to_bytes_bounds (int_rank.bitsize sz) sgn v /\
            vs = Z_to_bytes (int_rank.bitsize sz) sgn v
          | Vundef => pure_encodes_undef (int_rank.bitsize sz) vs
          | _ => False
          end
        | Tchar_ ct =>
          match v with
          | Vchar n =>
            (* Character values carry unsigned bit patterns. *)
            in_Z_to_bytes_bounds (char_type.bitsize ct) Unsigned (Z.of_N n) /\
            vs = Z_to_bytes (char_type.bitsize ct) Unsigned (Z.of_N n)
          | Vundef => pure_encodes_undef (char_type.bitsize ct) vs
          | _ => False
          end
        | Tmember_pointer _ _ =>
          match v with
          | Vint v =>
            (* note: this is really an offset *)
            in_Z_to_bytes_bounds (member_pointer_bitsize σ) Unsigned v /\
            vs = Z_to_bytes (member_pointer_bitsize σ) Unsigned v
          | Vundef => pure_encodes_undef (member_pointer_bitsize σ) vs
          | _ => False
          end
        | Tbool =>
          match v with
          | Vundef => vs = [Rundef]
          | _ =>
              if decide (v = Vint 0) then vs = [Rval 0%N]
              else if decide (v = Vint 1) then vs = [Rval 1%N]
              else False
          end
        | Tnullptr =>
          match v with
          | Vundef => pure_encodes_undef POINTER_BITSZ vs
          | _ => vs = cptr 0 /\ v = Vptr nullptr
          end
        | Tfloat_ ft =>
          match v with
          | Vfloat ft' f =>
              ft = ft' /\
              in_Z_to_bytes_bounds (float_type.bitsize ft') Unsigned (float_value.to_bits f) /\
              vs = Z_to_bytes (float_type.bitsize ft') Unsigned (float_value.to_bits f)
          | Vundef => pure_encodes_undef (float_type.bitsize ft) vs
          | _ => False
          end
        | Tarch _ _ => False
        | Tptr _ =>
          match v with
          | Vptr p =>
            if decide (p = nullptr) then
              vs = cptr 0
            else
              vs = aptr p
          | Vundef => pure_encodes_undef POINTER_BITSZ vs
          | _ => False
          end
        | Tfunction _
        | Tref _
        | Trv_ref _ =>
          match v with
          | Vptr p =>
            p <> nullptr /\
            vs = aptr p
          | Vundef => pure_encodes_undef POINTER_BITSZ vs
          | _ => False
          end
        | Tenum _ => False (* << TODO: incorrect *)
        | Tqualified _ _ => False (* unreachable *)
        | Tvoid
        | Tarray _ _
        | Tincomplete_array _
        | Tvariable_array _ _
        | Tnamed _ => False (* not directly encoded in memory *)
        | Tunsupported _ => False
        | Tdecltype _ => False
        | _ => False
        end.
      Definition encodes (t : type) (v : val) (vs : list runtime_val) : mpred :=
        [| pure_encodes t v vs |].

      #[global] Instance encodes_persistent : forall t v vs, Persistent (encodes t v vs) := _.

      #[global] Instance encodes_timeless : forall t v a, Timeless (encodes t v a) := _.

      #[local] Hint Resolve length_Z_to_bytes : core.
      #[local] Hint Resolve length_aptr : core.
      #[local] Hint Resolve length_cptr : core.
      #[local] Hint Resolve length_pure_encodes_undef : core.

      #[global] Instance encodes_nonvoid t v vs :
        Observe [| t <> Tvoid |] (encodes t v vs).
      Proof. apply: observe_intro_persistent; iIntros "!%". by destruct t. Qed.

      Lemma length_encodes t v vs :
        pure_encodes t v vs ->
          length vs = match erase_qualifiers t with
                      | Tbool => 1
                      | Tnum sz _ => int_rank.bytesNat sz
                      | Tchar_ ct => N.to_nat (char_type.bytesN ct)
                      | Tfloat_ ft => bitsize.bytesNat (float_type.bitsize ft)

                      | Tmember_pointer _ _ => bitsize.bytesNat (member_pointer_bitsize σ)
                      | Tnullptr | Tptr _
                      | Tfunction _ | Tref _ | Trv_ref _ =>
                                                 POINTER_BYTES

                      | _ => 1	(* dummy for absurd case, but useful for length_encodes_pos. *)
                      end.
      Proof.
        rewrite /pure_encodes => ?.
        destruct (erase_qualifiers _) => //;
          destruct v => //; destruct_and? => //;
          repeat case_decide => //;
           simplify_eq; eauto.
        all: try by destruct sz.
        all: try by destruct f.
        all: try (erewrite length_pure_encodes_undef; eauto; by destruct sz).
        all: try (erewrite length_pure_encodes_undef; eauto; by destruct f).
        - rewrite length_Z_to_bytes. by destruct t0.
        - erewrite length_pure_encodes_undef; last eassumption. by destruct t0.
      Qed.

      Lemma length_encodes_pos t v vs :
        pure_encodes t v vs ->
        length vs > 0.
      Proof.
        move=> /length_encodes ->. have ?: 1 > 0 by exact: le_n.
        induction t; simpl; try solve [ lia | exact: bytesNat_pos ].
        all: first [ destruct sz | destruct t ]; compute; lia.
      Qed.

      #[global] Instance Inj_aptr: Inj eq eq aptr.
      Proof.
        rewrite /aptr => p1 p2.
        by rewrite bytesNat_nnonnull'; csimpl => -[? _].
      Qed.

      Lemma pure_encodes_undef_aptr bitsz p :
        pure_encodes_undef bitsz (aptr p) -> False.
      Proof.
        rewrite /pure_encodes_undef /aptr.
        by rewrite (bytesNat_nnonnull' POINTER_BITSZ) (bytesNat_nnonnull' bitsz).
      Qed.

      Lemma pure_encodes_undef_Z_to_bytes bitsz sgn z :
        pure_encodes_undef bitsz (Z_to_bytes bitsz sgn z) ->
        False.
      Proof.
        rewrite /pure_encodes_undef /= bytesNat_nnonnull'.
        by edestruct Z_to_bytes_cons as (? & ? & ->).
      Qed.

      #[local] Hint Resolve pure_encodes_undef_aptr pure_encodes_undef_Z_to_bytes : core.

      #[global] Instance encodes_agree t v1 v2 vs :
        Observe2 [| v1 = v2 |] (encodes t v1 vs) (encodes t v2 vs).
      Proof.
        apply: observe_2_intro_persistent; rewrite /encodes /pure_encodes;
          iIntros (H1 H2) "!%".
        destruct (erase_qualifiers t) eqn:? =>//=; intros;
          repeat (try (case_decide || case_match); destruct_and?; simplify_eq => //);
        by [
          edestruct cptr_ne_aptr | edestruct pure_encodes_undef_aptr |
          edestruct pure_encodes_undef_Z_to_bytes |
          f_equal; apply N2Z.inj; exact: Z_to_bytes_inj |
          f_equal; apply float_value.to_bits_inj; exact: Z_to_bytes_inj |
          f_equiv; exact: Z_to_bytes_inj ].
      Qed.

      #[global] Instance encodes_consistent t v1 v2 vs1 vs2 :
        Observe2 [| length vs1 = length vs2 |] (encodes t v1 vs1) (encodes t v2 vs2).
      Proof. iIntros "!%". by move=> /length_encodes -> /length_encodes ->. Qed.
    End with_genv.

    Definition val_ (a : ptr) (v : val) q : mpred :=
      ghost_mem_own a q v.

    #[global] Instance val_agree a v1 v2 q1 q2 :
      Observe2 [| v1 = v2 |] (val_ a v1 q1) (val_ a v2 q2) := _.

    Lemma val_and_agree p v1 v2 q1 q2 :
      <absorb> (val_ p v1 q1) ∧ <absorb> (val_ p v2 q2) ⊢ ⌜v1 = v2⌝.
    Proof.
      rewrite /val_ /ghost_mem_own.
      apply CFracAgreement.cfrac_mpred_own_and_agree.
    Qed.

    #[global] Instance val_cfrac_valid a v :
      CFracValid0 (val_ a v).
    Proof. solve_cfrac_valid. Qed.

    Instance val_cfractional a rv : CFractional (val_ a rv) := _.
    Instance val_as_cfractional a rv q :
      AsCFractional (val_ a rv q) (val_ a rv) q := _.
    Instance val_timeless a rv q : Timeless (val_ a rv q) := _.
    Typeclasses Opaque val_.


    Definition byte_ (a : addr) (rv : runtime_val) q : mpred :=
      heap_own a q rv.

    #[global] Instance byte_agree a v1 v2 q1 q2 :
      Observe2 [|v1 = v2|] (byte_ a v1 q1) (byte_ a v2 q2) := _.

    Lemma byte_and_agree a v1 v2 q1 q2 :
      <absorb> (byte_ a v1 q1) ∧ <absorb> (byte_ a v2 q2) ⊢ ⌜v1 = v2⌝.
    Proof.
      rewrite /byte_ /heap_own.
      apply CFracAgreement.cfrac_mpred_own_and_agree.
    Qed.

    #[global] Instance byte_cfrac_valid a rv q :
      Observe [| q ≤ 1 |]%Qp (byte_ a rv q) := _.

    Instance byte_cfractional {a rv} : CFractional (byte_ a rv) := _.
    Instance byte_as_fractional a rv q :
      AsCFractional (byte_ a rv q) (fun q => byte_ a rv q) q := _.
    Instance byte_timeless {a rv q} : Timeless (byte_ a rv q) := _.

    Theorem byte_consistent a b b' q q' :
      byte_ a b q ** byte_ a b' q' |-- byte_ a b (q ⋅ q') ** [| b = b' |].
    Proof.
      iIntros "[Hb Hb']".
      iDestruct (byte_agree with "Hb Hb'") as %->.
      iCombine "Hb Hb'" as "Hb". by iFrame.
    Qed.

    Lemma byte_update (a : addr) (rv rv' : runtime_val) :
      byte_ a rv 1$m|-- |==> byte_ a rv' 1$m.
    Proof. by apply own_update, singleton_update, cmra_update_exclusive. Qed.

    Definition bytes (a : addr) (vs : list runtime_val) q : mpred :=
      [∗list] o ↦ v ∈ vs, byte_ (a+N.of_nat o)%N v q.

    Instance bytes_timeless a rv q : Timeless (bytes a rv q) := _.
    Instance bytes_fractional a vs : CFractional (bytes a vs) := _.
    Instance bytes_as_fractional a vs q :
      AsCFractional (bytes a vs q) (bytes a vs) q.
    Proof. solve_as_cfrac. Qed.
    Lemma bytes_nil a q : bytes a [] q -|- emp.
    Proof. done. Qed.

    Lemma bytes_cons a v vs q :
      bytes a (v :: vs) q -|- byte_ a v q ** bytes (N.succ a) vs q.
    Proof.
      rewrite /bytes big_sepL_cons /= N.add_0_r. do 2 f_equiv.
      move => ?. do 2 f_equiv. apply leibniz_equiv_iff. lia.
    Qed.

    Lemma bytes_agree {a vs1 vs2 q1 q2} :
      length vs1 = length vs2 →
      bytes a vs1 q1 ⊢ bytes a vs2 q2 -∗ ⌜vs1 = vs2⌝.
    Proof.
      revert a vs2. induction vs1 as [ |v vs1 IH]=> a vs2.
      { intros ->%symmetry%nil_length_inv. auto. }
      destruct vs2 as [ |v' vs2]; first done. intros [= Hlen].
      rewrite !bytes_cons.
      iIntros "[Hv Hvs1] [Hv' Hvs2] /=".
      iDestruct (byte_agree with "Hv Hv'") as %->.
      by iDestruct (IH _ _ Hlen with "Hvs1 Hvs2") as %->.
    Qed.

    Lemma bytes_and_agree a vs1 vs2 q1 q2 :
      length vs1 = length vs2 ->
      <absorb> (bytes a vs1 q1) ∧ <absorb> (bytes a vs2 q2) ⊢ ⌜vs1 = vs2⌝.
    Proof.
      intros Hlen. rewrite /bytes.
      apply CFracAgreement.big_sepL_and_agree; first exact Hlen.
      intros i x y. apply byte_and_agree.
    Qed.

    Lemma bytes_cfrac_valid a vs q :
      length vs > 0 ->
      bytes a vs q |-- [| q ≤ 1 |]%Qp.
    Proof.
      rewrite /bytes; case: vs => [ |v vs _] /=; first by lia.
      rewrite byte_cfrac_valid. by iIntros "[% _]".
    Qed.

    Lemma bytes_update {a : addr} {vs} vs' :
      length vs = length vs' →
      bytes a vs 1$m |-- |==> bytes a vs' 1$m.
    Proof.
      rewrite /bytes -big_sepL_bupd.
      revert a vs'.
      induction vs as [ | v vs IH]; intros a vs' EqL.
      { simplify_list_eq. symmetry in EqL. apply length_zero_iff_nil in EqL.
        by subst vs'. }
      destruct vs' as [ |v' vs'].
      { exfalso. done. }
      rewrite 2!big_sepL_cons. apply bi.sep_mono'.
      { by apply byte_update. }
      iPoseProof (IH (a + 1)%N vs') as "HL".
      { simpl in EqL. lia. }
      iIntros "By".
      iDestruct ("HL" with "[By]") as "By";
        iApply (big_sepL_mono with "By"); intros; simpl;
        rewrite (_: a + N.of_nat (S k) = a + 1 + N.of_nat k)%N //; lia.
    Qed.

    Instance mem_inj_own_agree p (oa1 oa2 : option N) :
      Observe2 [| oa1 = oa2 |] (mem_inj_own p oa1) (mem_inj_own p oa2).
    Proof.
      apply /observe_2_intro_persistent /bi.wand_intro_r.
      rewrite -own_op singleton_op.
      rewrite own_valid internal_cmra_valid_discrete singleton_valid.
      by iIntros "!%" => /= /to_agree_op_inv_L.
    Qed.

    Lemma mem_inj_and_agree p oa1 oa2 :
      <absorb> (mem_inj_own p oa1) ∧
      <absorb> (mem_inj_own p oa2) ⊢ ⌜oa1 = oa2⌝.
    Proof.
      rewrite !bi.absorbing_absorbingly bi.persistent_and_sep.
      iIntros "[H1 H2]".
      iDestruct (mem_inj_own_agree with "H1 H2") as %Hagree.
      done.
    Qed.

    Definition strict_valid_if_not_empty_array (ty : type) : ptr -> mpred :=
      if zero_sized_array ty then valid_ptr else strict_valid_ptr.
    #[global] Instance strict_valid_if_not_empty_array_persistent ty p :
      Persistent (strict_valid_if_not_empty_array ty p).
    Proof. rewrite /strict_valid_if_not_empty_array. case_match; refine _. Qed.
    #[global] Instance strict_valid_if_not_empty_array_affine ty p :
      Affine (strict_valid_if_not_empty_array ty p).
    Proof. rewrite /strict_valid_if_not_empty_array. case_match; refine _. Qed.
    #[global] Instance strict_valid_if_not_empty_array_timeless ty p :
      Timeless (strict_valid_if_not_empty_array ty p).
    Proof. rewrite /strict_valid_if_not_empty_array. case_match; refine _. Qed.

    Lemma zero_size_array_erase_qualifiers (ty : type) :
      zero_sized_array (erase_qualifiers ty) = zero_sized_array ty.
    Proof.
      induction ty; rewrite /= /qual_norm /=; eauto.
      - rewrite IHty. done.
      - rewrite IHty. clear.
        generalize (merge_tq QM q).
        clear. induction ty; rewrite /= /qual_norm/=; eauto.
        intros.
        rewrite -!IHty. done.
    Qed.

    Lemma strict_valid_if_not_empty_array_erase ty p :
      strict_valid_if_not_empty_array ty p
      -|- strict_valid_if_not_empty_array (erase_qualifiers ty) p.
    Proof.
      rewrite /strict_valid_if_not_empty_array.
      rewrite zero_size_array_erase_qualifiers. done.
    Qed.

    Definition has_type {σ : genv} (v : val) (ty : type) : mpred :=
      [| has_type_prop v ty |] **
      match v with
      | Vptr p =>
        match drop_qualifiers ty with
        | Tptr ty =>
          valid_ptr p ** [| aligned_ptr_ty ty p |]
        | Tref ty | Trv_ref ty =>
          strict_valid_if_not_empty_array ty p ** [| aligned_ptr_ty ty p |]
        | Tnullptr => [| p = nullptr |]
        | _ => emp
        end
      | _ => [| nonptr_prim_type ty |]
      end.

    Definition reference_to (ty : type) (p : ptr) : mpred :=
      [| aligned_ptr_ty ty p |] ** [| p <> nullptr |] **
        valid_ptr p ** if zero_sized_array ty then emp else strict_valid_ptr p.

    Definition has_type_or_undef (v : val) ty : mpred :=
      has_type v ty \\// [| v = Vundef |].
    Lemma has_type_or_undef_unfold :
      @has_type_or_undef = funI v ty => has_type v ty \\// [| v = Vundef |].
    Proof. done. Qed.

    Section with_genv.
      #[global] Instance has_type_knowledge : Knowledge2 has_type.
      Proof. solve_knowledge. Qed.

      #[global] Instance has_type_timeless : Timeless2 has_type.
      Proof.
        (* TODO AUTO: this gives a measureable speedup :-( *)
        have ?: Refine (Timeless (PROP := mpred) emp) by apply _.
        apply _.
      Qed.

      Lemma has_type_has_type_prop v ty :
        has_type v ty |-- [| has_type_prop v ty |].
      Proof. iIntros "[$ _]". Qed.

      Lemma has_type_prop_has_type_noptr v ty :
        nonptr_prim_type ty ->
        [| has_type_prop v ty |] |-- has_type v ty.
      Proof.
        rewrite /has_type /nonptr_prim_type; intros.
        iIntros "$".
        destruct v => //. by case_match.
      Qed.

      Lemma has_type_erase_qualifiers ty v :
        has_type v ty -|- has_type v (erase_qualifiers ty).
      Proof.
        rewrite /has_type has_type_prop_erase_qualifiers drop_erase_qualifiers.
        f_equiv.
        rewrite -nonptr_prim_type_erase_qualifiers.
        case_match; eauto.
        rewrite -erase_drop_qualifiers.
        case_match; simpl; eauto.
        all: try f_equiv.
        all: try rewrite aligned_ptr_ty_erase_qualifiers; auto.
        all: try apply strict_valid_if_not_empty_array_erase.
        exfalso; by eapply unqual_drop_qualifiers.
      Qed.

      Lemma has_type_nullptr' p :
        has_type (Vptr p) Tnullptr -|- [| p = nullptr |].
      Proof.
        rewrite /has_type/= has_type_prop_nullptr.
        rewrite (inj_iff Vptr).
        iSplit; first iIntros "[$ _]".
        iIntros "->". iSplit; eauto.
      Qed.

      Lemma has_type_ptr' p ty :
        has_type (Vptr p) (Tptr ty) -|- valid_ptr p ** [| aligned_ptr_ty ty p |].
      Proof.
        rewrite /has_type/= has_type_prop_pointer.
        rewrite only_provable_True ?(left_id emp) //. eauto.
      Qed.

      #[local] Instance strict_valid_ptr_nonnull p :
        Observe [| p <> nullptr |] (strict_valid_ptr p).
      Proof.
        iIntros "#? !>"; destruct (decide (p = nullptr)) as [-> | Hne]; last done.
        by rewrite not_strictly_valid_ptr_nullptr.
      Qed.

      Lemma has_type_ref' p ty :
        has_type (Vref p) (Tref ty) |-- reference_to ty p.
      Proof.
        rewrite /has_type/=/reference_to has_type_prop_ref.
        rewrite /strict_valid_if_not_empty_array.
        iIntros "[%Ht [#H $]]".
        destruct Ht as [? [Ht?]].
        inversion Ht; subst. case_match; iFrame "%#∗".
        by rewrite strict_valid_valid.
      Qed.

      Lemma has_type_rv_ref' p ty :
        has_type (Vref p) (Trv_ref ty) |-- reference_to ty p.
      Proof.
        rewrite -has_type_ref'.
        by rewrite /has_type/= has_type_prop_ref has_type_prop_rv_ref.
      Qed.

      #[global] Instance reference_to_knowledge : Knowledge2 reference_to.
      Proof.
        rewrite /reference_to. intros. case_match; split; refine _.
      Qed.
      #[global] Instance reference_to_timeless : Timeless2 reference_to.
      Proof. rewrite /reference_to. intros. case_match; refine _. Qed.

      Theorem reference_to_erase : forall ty p,
          reference_to ty p -|- reference_to (erase_qualifiers ty) p.
      Proof.
        rewrite /reference_to. intros.
        rewrite -aligned_ptr_ty_erase_qualifiers -zero_size_array_erase_qualifiers.
        done.
      Qed.

      Theorem reference_to_intro : forall ty p,
          strict_valid_ptr p |-- has_type (Vptr p) (Tptr ty) -* reference_to ty p.
      Proof.
        rewrite /has_type/reference_to/=.
        iIntros (??) "#V [%Htype [? %Haligned]]".
        iFrame "%".
        iDestruct (observe [| _ <> nullptr |] with "V") as "#$".
        iFrame. case_match; eauto.
      Qed.
      Theorem reference_to_elim : forall ty p,
          reference_to ty p |--
            [| aligned_ptr_ty ty p |] ** [| p <> nullptr |] **
            valid_ptr p ** if zero_sized_array ty then emp else strict_valid_ptr p.
      Proof. rewrite /reference_to. eauto. Qed.

    End with_genv.

    (** heap points to *)
    (* Auxiliary definitions.
      They're not exported, so we don't give them a complete theory;
      however, some of their proofs can be done via TC inference *)
    #[local] Definition addr_encodes
        (t : type) q (a : addr) (v : val) (vs : list runtime_val) :=
      encodes t v vs ** bytes a vs q ** vbytes a vs q.

    #[local] Instance addr_encodes_fractional ty a v vs :
      CFractional (λ q, addr_encodes ty q a v vs) := _.

    #[local] Instance addr_encodes_agree_dst t a v1 v2 vs1 vs2 q1 q2 :
      Observe2 [| vs1 = vs2 |]
        (addr_encodes t q1 a v1 vs1)
        (addr_encodes t q2 a v2 vs2).
    Proof.
      apply: observe_2_intro_persistent.
      iIntros "[En1 [By1 _]] [En2 [By2 _]]".
      iDestruct (encodes_consistent with "En1 En2") as %Heq.
      by iDestruct (bytes_agree Heq with "By1 By2") as %->.
    Qed.

    #[local] Instance addr_encodes_agree_src t v1 v2 a vs1 vs2 q1 q2 :
      Observe2 [| v1 = v2 |]
        (addr_encodes t q1 a v1 vs1)
        (addr_encodes t q2 a v2 vs2).
    Proof.
      iIntros "H1 H2".
      iDestruct (addr_encodes_agree_dst with "H1 H2") as %->.
      (* Using encodes_agree *)
      iApply (observe_2 with "H1 H2").
    Qed.

    Lemma addr_encodes_and_agree ty a v1 v2 vs1 vs2 q1 q2 :
      <absorb> (addr_encodes ty q1 a v1 vs1) ∧
      <absorb> (addr_encodes ty q2 a v2 vs2) ⊢ ⌜v1 = v2⌝.
    Proof.
      rewrite !bi.absorbing_absorbingly /addr_encodes !bi.sep_and.
      iIntros "H".
      iAssert (encodes ty v1 vs1) as "#E1".
      { iDestruct "H" as "[[E _] _]". iExact "E". }
      iAssert (encodes ty v2 vs2) as "#E2".
      { iDestruct "H" as "[_ [E _]]". iExact "E". }
      iDestruct (encodes_consistent with "E1 E2") as %Hlen.
      iAssert (⌜vs1 = vs2⌝)%I as %->.
      { iApply (bytes_and_agree _ _ _ _ _ Hlen). iSplit.
        - iDestruct "H" as "[[_ [B _]] _]". by iApply bi.absorbingly_intro.
        - iDestruct "H" as "[_ [_ [B _]]]". by iApply bi.absorbingly_intro. }
      iDestruct (encodes_agree with "E1 E2") as %Hagree.
      done.
    Qed.

    #[global] Instance addr_encodes_cfrac_valid ty :
      CFracValid3 (addr_encodes ty).
    Proof.
      constructor. intros. apply: observe_intro_persistent.
      iDestruct 1 as (Hen%length_encodes_pos) "[B _]".
      by iApply (bytes_cfrac_valid with "B").
    Qed.

    #[local] Definition oaddr_encodes
        (t : type) q (oa : option addr) p (v : val) :=
        match oa with
        | Some a =>
          Exists vs,
          addr_encodes t q a v vs
        | None => [| t <> Tvoid |] ** val_ p v q
        end.

    Lemma oaddr_encodes_and_agree ty oa p v1 v2 q1 q2 :
      <absorb> (oaddr_encodes ty q1 oa p v1) ∧
      <absorb> (oaddr_encodes ty q2 oa p v2) ⊢ ⌜v1 = v2⌝.
    Proof.
      destruct oa as [a|]; cbn [oaddr_encodes].
      - rewrite !bi.absorbingly_exist bi.and_exist_r.
        iDestruct 1 as (vs1) "H".
        iDestruct (bi.and_exist_l with "H") as (vs2) "H".
        by iApply addr_encodes_and_agree.
      - rewrite !bi.absorbingly_sep !bi.sep_and.
        iIntros "H". iApply val_and_agree. iSplit.
        + iDestruct "H" as "[[_ V] _]". iExact "V".
        + iDestruct "H" as "[_ [_ V]]". iExact "V".
    Qed.

    (* Needed by tptsto_cfractional *)
    #[local] Instance oaddr_encodes_fractional t oa p v :
      CFractional (λ q, oaddr_encodes t q oa p v).
    Proof. rewrite /oaddr_encodes; destruct oa; apply _. Qed.

    #[local] Instance oaddr_encodes_nonvoid ty q oa p v :
      Observe [| ty <> Tvoid |] (oaddr_encodes ty q oa p v).
    Proof. destruct oa; apply _. Qed.
    #[local] Instance oaddr_encodes_cfrac_valid t :
      CFracValid3 (oaddr_encodes t).
    Proof. constructor. intros ? oa ??. destruct oa; apply _. Qed.

    (** the pointer points to the code

      note that in the presence of code-loading, function calls will
      require an extra side-condition that the code is loaded.
     *)
    Definition code_own (p : ptr) (f : Func + Method + Ctor + Dtor) : mpred :=
      strict_valid_ptr p ** _code_own p f.
    Instance code_own_persistent f p : Persistent (code_own p f) := _.
    Instance code_own_affine f p : Affine (code_own p f) := _.
    Instance code_own_timeless f p : Timeless (code_own p f) := _.

    Lemma code_own_strict_valid f p : code_own p f ⊢ strict_valid_ptr p.
    Proof. iIntros "[$ _]". Qed.

    Lemma code_own_valid f p : code_own p f ⊢ valid_ptr p.
    Proof. by rewrite code_own_strict_valid strict_valid_valid. Qed.
    Typeclasses Opaque code_own.

    Definition code_at {_ : genv} (_ : translation_unit) (f : Func) (p : ptr) : mpred :=
      code_own p (inl (inl (inl f))).
    Definition method_at {_ : genv} (_ : translation_unit) (m : Method) (p : ptr) : mpred :=
      code_own p (inl (inl (inr m))).
    Definition ctor_at {_ : genv} (_ : translation_unit) (c : Ctor) (p : ptr) : mpred :=
      code_own p (inl (inr c)).
    Definition dtor_at {_ : genv} (_ : translation_unit) (d : Dtor) (p : ptr) : mpred :=
      code_own p (inr d).

    Instance code_at_persistent : forall tu f p, Persistent (code_at tu f p) := _.
    Instance code_at_affine : forall tu f p, Affine (code_at tu f p) := _.
    Instance code_at_timeless : forall tu f p, Timeless (code_at tu f p) := _.

    Instance method_at_persistent : forall tu f p, Persistent (method_at tu f p) := _.
    Instance method_at_affine : forall tu f p, Affine (method_at tu f p) := _.
    Instance method_at_timeless : forall tu f p, Timeless (method_at tu f p) := _.

    Instance ctor_at_persistent : forall tu f p, Persistent (ctor_at tu f p) := _.
    Instance ctor_at_affine : forall tu f p, Affine (ctor_at tu f p) := _.
    Instance ctor_at_timeless : forall tu f p, Timeless (ctor_at tu f p) := _.

    Instance dtor_at_persistent : forall tu f p, Persistent (dtor_at tu f p) := _.
    Instance dtor_at_affine : forall tu f p, Affine (dtor_at tu f p) := _.
    Instance dtor_at_timeless : forall tu f p, Timeless (dtor_at tu f p) := _.

    Axiom code_at_live   : forall tu f p,   code_at tu f p |-- live_ptr p.
    Axiom method_at_live : forall tu f p, method_at tu f p |-- live_ptr p.
    Axiom ctor_at_live   : forall tu f p,   ctor_at tu f p |-- live_ptr p.
    Axiom dtor_at_live   : forall tu f p,   dtor_at tu f p |-- live_ptr p.

    Section with_genv.
      Lemma code_at_strict_valid tu f p :   code_at tu f p |-- strict_valid_ptr p.
      Proof. exact: code_own_strict_valid. Qed.
      Lemma method_at_strict_valid tu f p :   method_at tu f p |-- strict_valid_ptr p.
      Proof. exact: code_own_strict_valid. Qed.
      Lemma ctor_at_strict_valid tu f p :   ctor_at tu f p |-- strict_valid_ptr p.
      Proof. exact: code_own_strict_valid. Qed.
      Lemma dtor_at_strict_valid tu f p :   dtor_at tu f p |-- strict_valid_ptr p.
      Proof. exact: code_own_strict_valid. Qed.
    End with_genv.

    (** physical representation of pointers.
    OLD, not exposed any more.
     *)
    #[local] Definition pinned_ptr (va : N) (p : ptr) : mpred :=
      valid_ptr p **
      ([| p = nullptr /\ va = 0%N |] \\//
      ([| p <> nullptr /\ ptr_vaddr p = Some va |] ** mem_inj_own p (Some va))).

    Lemma pinned_ptr_null : |-- pinned_ptr 0 nullptr.
    Proof. iSplit; by [iApply valid_ptr_nullptr | iLeft]. Qed.

    Definition type_ptr {resolve : genv} (ty : type) (p : ptr) : mpred :=
      [| p <> nullptr |] **
      [| aligned_ptr_ty ty p |] **
      [| is_Some (size_of resolve ty) |] **

      strict_valid_ptr p ** valid_ptr (p ,, o_sub resolve ty 1).
      (* TODO: inline valid_ptr, and assert validity of the range, like we should do in tptsto!
      For 0-byte objects, should we assert ownership of one byte, to get character pointers? *)
      (* [alloc_own (alloc_id p) (l, h) **
      [| l <= ptr_addr p <= ptr_addr (p ,, o_sub resolve ty 1) <= h |]] *)

    Instance type_ptr_persistent σ p ty : Persistent (type_ptr ty p) := _.
    Instance type_ptr_affine σ p ty : Affine (type_ptr ty p) := _.
    Instance type_ptr_timeless σ p ty : Timeless (type_ptr ty p) := _.

    Lemma type_ptr_off_nonnull {ty p o} :
      type_ptr ty (p ,, o) |-- [| p <> nullptr |].
    Proof.
      iDestruct 1 as "(_ & _ & _ & H & _)".
      by iApply strict_valid_ptr_off_nonnull.
    Qed.

    Lemma type_ptr_strict_valid ty p :
      type_ptr ty p |-- strict_valid_ptr p.
    Proof. iDestruct 1 as "(_ & _ & _ & $ & _)". Qed.

    Lemma type_ptr_valid_plus_one ty p :
      (* size_of resolve ty = Some sz -> *)
      type_ptr ty p |--
      valid_ptr (p ,, o_sub σ ty 1).
    Proof. iDestruct 1 as "(_ & _ & _ & _ & $)". Qed.

    Section subscript_validity.
      #[local] Open Scope Z_scope.
      Lemma type_ptr_subscript_valid ty p sz elem esz (i : Z) vt :
        size_of σ ty = Some sz ->
        size_of σ elem = Some esz ->
        0 <= Z.of_N esz * i <= Z.of_N sz ->
        (vt = pred.Strict -> Z.of_N esz * i = 0 \/ Z.of_N esz * i < Z.of_N sz) ->
        type_ptr ty p ⊢ _valid_ptr vt (p ,, o_sub σ elem i).
      Proof.
        intros Hsz Hes Hrange Hstrict.
        iDestruct 1 as "(_ & _ & _ & V0 & V1)".
        iDestruct (_valid_ptr_offset_defined with "V0") as %Hdef.
        destruct p as [|root off]; first contradiction.
        rewrite /_valid_ptr.
        iDestruct "V0" as "[[_ %Hbad]|V0]"; first discriminate.
        iDestruct "V0" as (l h) "(B0 & %Haid & %Hpath)".
        iDestruct "V1" as "[[%Hnull _]|V1]".
        { exfalso. apply (f_equal ptr_alloc_id) in Hnull.
          rewrite _dot.unlock /DOT_dot /= in Hnull.
          destruct Haid as (aid & Haid & Hneq).
          rewrite Hnull in Haid. injection Haid as <-. contradiction. }
        rewrite _dot.unlock /DOT_dot /=.
        iDestruct "V1" as (l' h') "(B1 & _ & %Hend)".
        iDestruct (blocks_own_range_agree with "[$B0 $B1]") as %Erange.
        injection Erange as <- <-.
        iRight. iExists l, h. iFrame "B0". iSplit; first done.
        iPureIntro.
        destruct (raw_path_valid_end _ _ _ _ _ Hpath)
          as (z0 & va0 & E0 & A0 & N0 & R0).
        destruct (raw_path_valid_end _ _ _ _ _ Hend)
          as (z1 & va1 & E1 & A1 & N1 & R1).
        have Eend := eval_offset_dot σ off (o_sub σ ty 1) z0 (Z.of_N sz * 1)
          E0 (eval_o_sub' σ ty 1 sz Hsz).
        rewrite _dot.unlock /DOT_dot /eval_offset /= in Eend.
        rewrite Eend in E1. injection E1 as <-.
        have Hb : z0 + Z.of_N esz * i < h \/
            (vt = pred.Relaxed /\ z0 + Z.of_N esz * i = h).
        { destruct vt.
          - have Hs := Hstrict eq_refl. left. destruct Hs as [Hs|Hs].
            + destruct R0 as [R0|[Hbad _]]; [lia|discriminate].
            + destruct R1 as [R1|[_ R1]]; lia.
          - destruct (decide (z0 + Z.of_N esz * i < h)) as [Hlt|Hlt];
              first by left.
            right. split; first done. destruct R1 as [R1|[_ R1]]; lia. }
        destruct (offset_subscript_decompose σ off elem esz Hdef Hes)
          as (prefix & n & d & _ & _ & _ & E).
        have Ezero := E 0.
        have Eid : off ,, o_id = off.
        { rewrite _dot.unlock /DOT_dot. apply __o_dot_id. }
        rewrite (o_sub_0 σ elem (ex_intro _ esz Hes)) Eid in Ezero.
        rewrite ?Z.add_0_r ?Z.mul_0_r ?Z.add_0_r in Ezero.
        rewrite _dot.unlock /DOT_dot /= in E.
        rewrite Ezero in Hpath, E0. rewrite E.
        exact (raw_path_valid_subscript_increase vt root l h prefix
          (erase_qualifiers elem) n d (n+i) (Z.of_N esz * i) z0
          Hpath E0 (proj1 Hrange) Hb).
      Qed.
      Lemma aligned_ptr_ty_subscript resolve p ty sz i :
        size_of resolve ty = Some sz ->
        @aligned_ptr_ty resolve ty p ->
        is_Some (@ptr_vaddr resolve p) ->
        aligned_ptr_ty ty (p ,, o_sub resolve ty i).
      Proof.
        intros Hsz [al [Hal Halp]] [va Hva].
        exists al. split; first done.
        destruct (ptr_vaddr (p ,, o_sub resolve ty i)) as [va'|] eqn:Hva'; last by right.
        left. exists va'. split; first done.
        have Hsum := ptr_vaddr_offset_add resolve p (o_sub resolve ty i) va va'
          (Z.of_N sz * i) Hva Hva' (eval_o_sub' resolve ty i sz Hsz).
        destruct Halp as [[base [Hbase Hdva]]|Hnone]; last congruence.
        have Ebase : base = va by congruence. subst base.
        destruct (align_of_size_of' ty sz Hsz) as (al' & Hal' & Hnz & Hdvd).
        have Eal : al' = al by congruence. subst al'.
        have Hz : (Z.of_N al | Z.of_N va')%Z.
        { rewrite Hsum. apply Z.divide_add_r.
          - exact: N2Z_inj_divide.
          - apply Z.divide_mul_l. exact: N2Z_inj_divide. }
        have Hpos : (0 < Z.of_N al)%Z by lia.
        have Hnn : (0 <= Z.of_N va')%Z by lia.
        move: (Z2N_inj_divide _ _ Hpos Hnn Hz). by rewrite !N2Z.id.
      Qed.
    End subscript_validity.

    Lemma aligned_ptr_ty_base resolve p derived base dsz bsz dal bal z :
      size_of resolve (Tnamed derived) = Some dsz ->
      size_of resolve (Tnamed base) = Some bsz ->
      @align_of resolve (Tnamed derived) = Some dal ->
      @align_of resolve (Tnamed base) = Some bal ->
      parent_offset resolve derived base = Some z ->
      (bal | dal)%N -> (Z.of_N bal | z)%Z ->
      @aligned_ptr_ty resolve (Tnamed derived) p ->
      is_Some (@ptr_vaddr resolve p) ->
      aligned_ptr_ty (Tnamed base) (p ,, o_base resolve derived base).
    Proof.
      intros Hds Hbs Hda Hba Hz Hdiv Hdz [al [Hal Halp]] [va Hva].
      have Eal : al = dal by congruence. subst al.
      exists bal. split; first done.
      destruct (ptr_vaddr (p ,, o_base resolve derived base)) as [va'|] eqn:Hva'; last by right.
      left. exists va'. split; first done.
      have Hsum := ptr_vaddr_offset_add resolve p (o_base resolve derived base) va va' z
        Hva Hva' (eval_o_base' resolve derived base z Hz).
      destruct Halp as [[a [Ha Hda']]|Hnone]; last congruence.
      have Ea : a = va by congruence. subst a.
      have Hdva : (bal | va)%N := N.divide_trans _ _ _ Hdiv Hda'.
      destruct (align_of_size_of' (Tnamed base) bsz Hbs) as (al & Habal & Hnz & _).
      have Eal : al = bal by congruence. subst al.
      have Hdiv' : (Z.of_N bal | Z.of_N va')%Z.
      { rewrite Hsum. apply Z.divide_add_r; [exact: N2Z_inj_divide|exact Hdz]. }
      have Hp : (0 < Z.of_N bal)%Z by lia.
      have Hnn : (0 <= Z.of_N va')%Z by lia.
      move: (Z2N_inj_divide _ _ Hp Hnn Hdiv'). by rewrite !N2Z.id.
    Qed.

    Lemma type_ptr_erase : forall ty p,
        type_ptr ty p -|- type_ptr (erase_qualifiers ty) p.
    Proof.
      rewrite /type_ptr; intros.
      by rewrite -aligned_ptr_ty_erase_qualifiers size_of_erase_qualifiers o_sub_erase.
    Qed.

    Lemma type_ptr_aligned_pure ty p :
      type_ptr ty p |-- [| aligned_ptr_ty ty p |].
    Proof. iDestruct 1 as "(_ & $ & _)". Qed.

    Lemma type_ptr_size ty p : type_ptr ty p |-- [| is_Some (size_of σ ty) |].
    Proof. iDestruct 1 as "(_ & _ & % & _)"; eauto. Qed.



    (* todo(gmm): this isn't accurate, but it is sufficient to show that the axioms are
    instantiatable. *)
    Definition mdc_path {_ : genv} (this : globname) (most_derived : list globname)
               (q : cQp.t) (p : ptr) : mpred :=
      strict_valid_ptr p ** derivation_own p q this most_derived.

    Instance mdc_path_cfractional this mdc : CFractional1 (mdc_path this mdc) := _.
    Lemma mdc_path_cfrac_valid : forall cls path,
      CFracValid1 (mdc_path cls path).
    Proof. intros cls path. solve_cfrac_valid. Qed.
    Instance mdc_path_timeless this mdc q p : Timeless (mdc_path this mdc q p) := _.
    Instance mdc_path_strict_valid this mdc q p : Observe (strict_valid_ptr p) (mdc_path this mdc q p).
    Proof. refine _. Qed.
    Instance mdc_path_agree cls1 cls2 q1 q2 p mdc1 mdc2 :
      Observe2 [| mdc1 = mdc2 /\ cls1 = cls2 |] (mdc_path cls1 mdc1 q1 p) (mdc_path cls2 mdc2 q2 p).
    Proof.
      rewrite /mdc_path.
      iIntros "[_ A] [_ B]".
      iDestruct (observe_2 [| _ = _ |] with "A B") as %Heq; inversion Heq; eauto.
    Qed.

    (** this allows you to forget an object mdc_path, necessary for doing
        placement [new] over an existing object.
     *)
    Theorem mdc_path_forget : forall mdc this p,
        mdc_path this mdc 1$m p |-- |={↑pred_ns}=> mdc_path this nil 1$m p.
    Proof.
      rewrite /mdc_path; intros.
      iIntros "[$ D]".
      iDestruct (own_update with "D") as ">$"; eauto.
      by apply singleton_update, cmra_update_exclusive.
    Qed.

    Definition tptsto (t : type) (q : cQp.t) (p : ptr) (v : val) : mpred :=
      [| p <> nullptr |] ** [| is_heap_type t |] **
      Exists (oa : option addr),
        type_ptr t p ** (* use the appropriate ghost state instead *)
        mem_inj_own p oa **
        oaddr_encodes t q oa p v ** has_type_or_undef v t.
    (* TODO: [tptsto] should not include [type_ptr] wholesale, but its
    pieces in the new model, replacing [mem_inj_own], and [tptsto_type_ptr]
    should be proved properly. *)

    #[global] Instance tptsto_valid_type
      : forall (t : type) (q : cQp.t) (a : ptr) (v : val),
        Observe [| is_heap_type t |] (tptsto t q a v).
    Proof. rewrite /tptsto; refine _. Qed.

    #[global] Instance tptsto_type_ptr : forall ty q p v,
        Observe (type_ptr ty p) (tptsto ty q p v) := _.

    (* TODO (JH): We shouldn't be axiomatizing this in our model in the long-run *)
    Axiom tptsto_live : forall ty (q : cQp.t) p v,
      tptsto ty q p v |-- live_ptr p ** True.

    #[global] Instance tptsto_nonnull_obs ty q a :
      Observe False (tptsto ty q nullptr a).
    Proof. iDestruct 1 as (Hne) "_". naive_solver. Qed.

    Theorem tptsto_nonnull ty q a :
      tptsto ty q nullptr a |-- False.
    Proof. rewrite tptsto_nonnull_obs. iDestruct 1 as "[]". Qed.

    (* Relies on [oaddr_encodes_fractional] *)
    #[global] Instance tptsto_cfractional ty : CFractional2 (tptsto ty) := _.

    #[global] Instance tptsto_timeless ty q p v :
      Timeless (tptsto ty q p v) := _.

    #[global] Instance tptsto_nonvoid ty (q : cQp.t) p v :
      Observe [| ty <> Tvoid |] (tptsto ty q p v) := _.

    #[global] Instance tptsto_cfrac_valid ty :
      CFracValid2 (tptsto ty).
    Proof. solve_cfrac_valid. Qed.

    Lemma val_update (p : ptr) (v v' : val) :
      val_ p v 1$m |-- |==> val_ p v' 1$m.
    Proof. by apply own_update, singleton_update, cmra_update_exclusive. Qed.

    Lemma tptsto_ghost_intro ty q p v :
      is_heap_type ty ->
      type_ptr ty p ** mem_inj_own p None ** val_ p v q **
      has_type_or_undef v ty |-- tptsto ty q p v.
    Proof.
      intros Hheap. iIntros "(#T & #M & V & #Hv)".
      iAssert [| p <> nullptr |] as %Hnn.
      { iDestruct "T" as "[$ _]". }
      iAssert [| ty <> Tvoid |] as %Hnv.
      { iDestruct (type_ptr_size with "T") as %Hsize.
        iPureIntro. intros ->. destruct Hsize as [sz Hsize]. discriminate. }
      rewrite /tptsto. iSplit; first done. iSplit; first done.
      iExists None. iFrame "T M Hv". iFrame "V". done.
    Qed.

    Lemma tptsto_physical_intro ty q p v a vs :
      is_heap_type ty ->
      type_ptr ty p ** mem_inj_own p (Some a) ** encodes ty v vs **
      bytes a vs q ** vbytes a vs q ** has_type_or_undef v ty |--
      tptsto ty q p v.
    Proof.
      intros Hheap. iIntros "(#T & #M & E & B & V & #Hv)".
      iAssert [| p <> nullptr |] as %Hnn.
      { iDestruct "T" as "[$ _]". }
      rewrite /tptsto. iSplit; first done. iSplit; first done.
      iExists (Some a). iFrame "T M Hv". iExists vs. iFrame.
    Qed.

    Lemma tptsto_ghost_update ty p v v' :
      mem_inj_own p None ** tptsto ty 1$m p v ** has_type_or_undef v' ty |--
      |==> tptsto ty 1$m p v'.
    Proof.
      iIntros "(#M & H & #Hv)".
      iDestruct "H" as (Hnn Hheap oa) "(#T & #M' & E & _)".
      iDestruct (mem_inj_own_agree with "M M'") as %<-.
      iDestruct "E" as "[_ V]".
      iMod (val_update with "V") as "V".
      iModIntro. iApply tptsto_ghost_intro; first exact Hheap.
      iFrame "T M V Hv".
    Qed.


    Lemma tptsto_view ty q p v :
      tptsto ty q p v ⊢
      ∃ oa, mem_inj_own p oa ∗ oaddr_encodes ty q oa p v.
    Proof.
      iDestruct 1 as (Hnn Hheap oa) "(_ & M & E & _)".
      iExists oa. iFrame.
    Qed.

    Lemma tptsto_agree_and ty q1 q2 p v1 v2 :
      <absorb> (tptsto ty q1 p v1) ∧
      <absorb> (tptsto ty q2 p v2) ⊢ ⌜v1 = v2⌝.
    Proof.
      rewrite !tptsto_view !bi.absorbingly_exist bi.and_exist_r.
      iDestruct 1 as (oa1) "H".
      iDestruct (bi.and_exist_l with "H") as (oa2) "H".
      iEval (rewrite !bi.absorbingly_sep !bi.sep_and) in "H".
      iAssert (⌜oa1 = oa2⌝)%I as %->.
      { iApply mem_inj_and_agree. iSplit.
        - iDestruct "H" as "[[M _] _]". iExact "M".
        - iDestruct "H" as "[_ [M _]]". iExact "M". }
      iApply oaddr_encodes_and_agree. iSplit.
      - iDestruct "H" as "[[_ E] _]". iExact "E".
      - iDestruct "H" as "[_ [_ E]]". iExact "E".
    Qed.

    #[global] Instance tptsto_agree ty q1 q2 p v1 v2 :
      Observe2 [| v1 = v2 |] (tptsto ty q1 p v1) (tptsto ty q2 p v2).
    Proof.
      apply observe_2_intro_only_provable.
      iIntros "P Q". iApply (tptsto_agree_and ty q1 q2 p v1 v2).
      iSplit.
      - iApply bi.absorbingly_intro. iExact "P".
      - iApply bi.absorbingly_intro. iExact "Q".
    Qed.

    Lemma offset_pinned_ptr_pure : forall σ o z va p,
      eval_offset σ o = Some z ->
      pinned_ptr_pure va p ->
      valid_ptr (p ,, o) |--
      [| 0 <= Z.of_N va + z |]%Z **
      [| ptr_vaddr (p ,, o) = Some (Z.to_N (Z.of_N va + z)) |].
    Proof.
      intros σ' o z va p Ho Hp. iIntros "V".
      iDestruct (_valid_ptr_vaddr (resolve:=σ') with "V") as %(va' & Haddr).
      have Hsum := ptr_vaddr_offset_add σ' p o va va' z Hp Haddr Ho.
      iSplit; iPureIntro.
      - lia.
      - by rewrite -Hsum N2Z.id.
    Qed.

    Lemma offset_inv_pinned_ptr_pure_guarded : forall σ o z va p,
      eval_offset σ o = Some z ->
      pinned_ptr_pure va (p ,, o) ->
      valid_ptr p |--
      [| 0 <= Z.of_N va - z |]%Z **
      [| pinned_ptr_pure (Z.to_N (Z.of_N va - z)) p |].
    Proof.
      intros σ' o z va p Ho Hp. iIntros "V".
      iDestruct (_valid_ptr_vaddr (resolve:=σ') with "V") as %(va' & Haddr).
      have Hsum := ptr_vaddr_offset_add σ' p o va' va z Haddr Hp Ho.
      have Hdiff : (Z.of_N va - z = Z.of_N va')%Z by lia.
      iSplit; iPureIntro.
      - lia.
      - by rewrite /pinned_ptr_pure Hdiff N2Z.id.
    Qed.

    Lemma offset_inv_pinned_ptr_pure : forall σ o z va p,
      eval_offset σ o = Some z ->
      pinned_ptr_pure va (p ,, o) ->
      valid_ptr p |--
      [| 0 <= Z.of_N va - z |]%Z **
      [| pinned_ptr_pure (Z.to_N (Z.of_N va - z)) p |].
    Proof. apply offset_inv_pinned_ptr_pure_guarded. Qed.

    (** Checked interpolation uses canonical root ranges and retains zero-stride
        boundary validity. Strict interpolation requires positive byte stride. *)
    Lemma _valid_ptr_sub (i j k : Z) (p : ptr) ty vt1 vt2 vt :
      (i <= j < k)%Z ->
      (vt = pred.Strict -> exists sz, size_of σ ty = Some sz /\ (0 < sz)%N) ->
      _valid_ptr vt1 (p ,, o_sub σ ty i) ⊢
      _valid_ptr vt2 (p ,, o_sub σ ty k) -∗ _valid_ptr vt (p ,, o_sub σ ty j).
    Proof.
      intros Hijk Hpositive. iIntros "Vi Vk".
      iDestruct (_valid_ptr_offset_defined with "Vi") as %Hdefined.
      apply (ptr_offset_defined_dot σ) in Hdefined as [Hp Hsub].
      have [sz Hsz] := eval_o_sub_defined σ ty i Hsub.
      have Hpos : vt = pred.Strict -> (0 < sz)%N.
      { intros E. destruct (Hpositive E) as (s & Hs & Hpos).
        rewrite Hsz in Hs. injection Hs as <-. exact Hpos. }
      destruct p as [|root off]; first contradiction.
      have Hnullid (x : Z) : (offset_ptr root off : ptr) ,, o_sub σ ty x = nullptr ->
          root_ptr_alloc_id root = Some null_alloc_id.
      { intros E. apply (f_equal ptr_alloc_id) in E.
        by rewrite _dot.unlock /DOT_dot /= in E. }
      rewrite /_valid_ptr.
      iDestruct "Vi" as "[[%Hni _]|Vi]";
        iDestruct "Vk" as "[[%Hnk _]|Vk]".
      - exfalso. have E := subscript_null_inj σ (offset_ptr root off) ty i k Hni Hnk. lia.
      - rewrite _dot.unlock /DOT_dot /=.
        iDestruct "Vk" as (l h) "(_ & %Haid & _)".
        exfalso. destruct Haid as (aid & Haid & Hneq).
        rewrite (Hnullid i Hni) in Haid. injection Haid as <-. contradiction.
      - rewrite _dot.unlock /DOT_dot /=.
        iDestruct "Vi" as (l h) "(_ & %Haid & _)".
        exfalso. destruct Haid as (aid & Haid & Hneq).
        rewrite (Hnullid k Hnk) in Haid. injection Haid as <-. contradiction.
      - rewrite _dot.unlock /DOT_dot /=.
        iDestruct "Vi" as (l h) "(Bi & %Haid & %Hpi)".
        iDestruct "Vk" as (l' h') "(Bk & _ & %Hpk)".
        iDestruct (blocks_own_range_agree with "[$Bi $Bk]") as %Erange.
        injection Erange as <- <-.
        iRight. iExists l, h. iFrame "Bi". iSplit; first done.
        iPureIntro.
        destruct (offset_subscript_decompose σ off ty sz Hp Hsz)
          as (prefix & n & d & _ & _ & _ & E).
        rewrite _dot.unlock /DOT_dot /= in E.
        rewrite (E i) in Hpi. rewrite (E k) in Hpk. rewrite (E j).
        exact (raw_path_valid_subscript_interpolate vt1 vt2 vt root l h
          prefix (erase_qualifiers ty) n d sz i j k Hijk Hpos Hpi Hpk).
    Qed.

    Lemma strict_valid_ptr_sub_guarded : ∀ (i j k : Z) p ty vt1 vt2,
      (i <= j < k)%Z ->
      (exists sz, size_of σ ty = Some sz /\ (0 < sz)%N) ->
      _valid_ptr vt1 (p ,, o_sub σ ty i) |--
      _valid_ptr vt2 (p ,, o_sub σ ty k) -* strict_valid_ptr (p ,, o_sub σ ty j).
    Proof.
      intros i j k p ty vt1 vt2 Hijk Hsize.
      apply (_valid_ptr_sub i j k p ty vt1 vt2 Strict Hijk).
      intros _. exact Hsize.
    Qed.

    #[local] Lemma type_ptr_base_layout derived base p dsz bsz dal bal z :
      size_of σ (Tnamed derived) = Some dsz ->
      size_of σ (Tnamed base) = Some bsz ->
      @align_of σ (Tnamed derived) = Some dal ->
      @align_of σ (Tnamed base) = Some bal ->
      parent_offset σ derived base = Some z ->
      (bal | dal)%N -> (Z.of_N bal | z)%Z ->
      (0 <= z)%Z -> (z = 0 \/ z < Z.of_N dsz)%Z ->
      (z + Z.of_N bsz <= Z.of_N dsz)%Z ->
      type_ptr (Tnamed derived) p ⊢
      type_ptr (Tnamed base) (p ,, o_base σ derived base).
    Proof.
      intros Hds Hbs Hda Hba Hz Hdiv Hdz Hnonneg Hstrict Hbound.
      iIntros "#T".
      iDestruct (type_ptr_aligned_pure with "T") as %Hal.
      iDestruct (type_ptr_strict_valid with "T") as "V0".
      iDestruct (_valid_ptr_vaddr (resolve:=σ) with "V0") as %Hva.
      have Halbase := aligned_ptr_ty_base σ p derived base dsz bsz dal bal z
        Hds Hbs Hda Hba Hz Hdiv Hdz Hal Hva.
      iDestruct (type_ptr_valid_plus_one with "T") as "V1".
      iDestruct (_valid_ptr_offset_defined with "V0") as %Hdef.
      destruct p as [|root off]; first contradiction.
      rewrite /_valid_ptr.
      iDestruct "V0" as "[[_ %Hbad]|V0]"; first discriminate.
      iDestruct "V0" as (l h) "(#B0 & %Haid & %Hpath)".
      iDestruct "V1" as "[[%Hnull _]|V1]".
      { exfalso. apply (f_equal ptr_alloc_id) in Hnull.
        rewrite _dot.unlock /DOT_dot /= in Hnull.
        destruct Haid as (aid & Haid & Hneq).
        rewrite Hnull in Haid. injection Haid as <-. contradiction. }
      rewrite _dot.unlock /DOT_dot /=.
      iDestruct "V1" as (l' h') "(B1 & _ & %Hend)".

      iDestruct (blocks_own_range_agree (lift_root_ptr root) l h l' h' with "[$B0 $B1]") as %Erange.
      injection Erange as <- <-.
      destruct (raw_path_valid_end _ _ _ _ _ Hpath)
        as (z0 & va0 & E0 & A0 & N0 & R0).
      destruct (raw_path_valid_end _ _ _ _ _ Hend)
        as (z1 & va1 & E1 & A1 & N1 & R1).
      have Eend := eval_offset_dot σ off (o_sub σ (Tnamed derived) 1) z0 (Z.of_N dsz * 1)
        E0 (eval_o_sub' σ (Tnamed derived) 1 dsz Hds).
      rewrite _dot.unlock /DOT_dot /eval_offset /= in Eend.
      rewrite Eend in E1. injection E1 as <-.
      have Hb : (z0+z < h)%Z.
      { destruct R0 as [R0|[Hbad _]]; last discriminate.
        destruct Hstrict as [->|Hstrict]; first lia.
        destruct R1 as [R1|[_ R1]]; lia. }
      have Hbase : raw_path_valid pred.Strict root l h
        (proj1_sig (__o_dot off (o_base σ derived base))).
      { have Eraw := offset_base_raw σ off derived base z Hz.
        rewrite _dot.unlock /DOT_dot in Eraw. rewrite Eraw.
        apply (raw_path_valid_base_increase pred.Strict root l h (proj1_sig off) derived base z0 z);
          try done; first exact (proj2_sig off).
        by left. }
      have Ebase := eval_offset_dot σ off (o_base σ derived base) z0 z E0
        (eval_o_base' σ derived base z Hz).
      rewrite _dot.unlock /DOT_dot in Ebase.
      have Hbaseend : raw_path_valid pred.Relaxed root l h
        (proj1_sig (__o_dot (__o_dot off (o_base σ derived base)) (o_sub σ (Tnamed base) 1))).
      { have Hbd : is_Some (eval_offset σ (__o_dot off (o_base σ derived base))).
        { exists (z0+z)%Z. exact Ebase. }
        destruct (offset_subscript_decompose σ (__o_dot off (o_base σ derived base))
          (Tnamed base) bsz Hbd Hbs) as (prefix & n & d & _ & _ & _ & E).
        have Ezero := E 0.
        have Eid : forall o : offset, o ,, o_id = o.
        { intros o. rewrite _dot.unlock /DOT_dot. apply __o_dot_id. }
        rewrite (o_sub_0 σ (Tnamed base) (ex_intro _ bsz Hbs)) Eid in Ezero.
        rewrite ?Z.add_0_r ?Z.mul_0_r ?Z.add_0_r in Ezero.
        rewrite _dot.unlock /DOT_dot /= in E.
        rewrite /eval_offset in Ebase.
        rewrite Ezero in Hbase, Ebase. have Eone := E 1. rewrite /= in Eone.
        rewrite /__o_dot /= Eone.
        apply (raw_path_valid_subscript_increase pred.Relaxed root l h prefix
          (Tnamed base) n d (n+1) (Z.of_N bsz*1) (z0+z)); try done; try lia.
        destruct (decide (z0+z+Z.of_N bsz*1 < h)%Z) as [Hlt|Hlt]; first by left.
        right. split; first done. destruct R1 as [R1|[_ R1]]; lia. }
      rewrite /type_ptr.
      iSplit.
      { iPureIntro. intros E. apply (f_equal ptr_alloc_id) in E.
        simpl in E.
        destruct Haid as (aid & Haid & Hneq).
        rewrite E in Haid. injection Haid as <-. contradiction. }
      iSplit.
      { iPureIntro. rewrite _dot.unlock /DOT_dot in Halbase. exact Halbase. }
      iSplit; first (iPureIntro; by exists bsz).
      rewrite /_valid_ptr _dot.unlock /DOT_dot /=.
      iSplit; iRight; iExists l,h; iFrame "B0"; iSplit; done.
    Qed.

    Lemma type_ptr_o_base_guarded derived base p :
      class_derives derived [base] ->
      base_layout_compatible σ derived base ->
      type_ptr (Tnamed derived) p ⊢ type_ptr (Tnamed base) (p ,, o_base σ derived base).
    Proof.
      intros _ (dsz & bsz & dal & bal & z & Hds & Hbs & Hda & Hba & Hz & Hd & Hdz & Hnn & Hs & Hb).
      exact (type_ptr_base_layout derived base p dsz bsz dal bal z
        Hds Hbs Hda Hba Hz Hd Hdz Hnn Hs Hb).
    Qed.

  End with_cpp.

    Parameter exposed_aid : forall `{!cpp_logic thread_info Σ}, alloc_id -> mpred.

  Section with_cpp.
    Context `{!cpp_logic thread_info Σ} {σ}.
    (* strict validity (not past-the-end) *)
    Notation strict_valid_ptr := (_valid_ptr Strict).
    (* relaxed validity (past-the-end allowed) *)
    Notation valid_ptr := (_valid_ptr Relaxed).

    Axiom exposed_aid_persistent : forall aid, Persistent (exposed_aid aid).
    Lemma exposed_aid_affine : forall aid, Affine (exposed_aid aid).
    Proof. intros. pose proof mpred_BiAffine. apply _. Qed.
    Axiom exposed_aid_timeless : forall aid, Timeless (exposed_aid aid).

    Axiom exposed_aid_null_alloc_id : |-- exposed_aid null_alloc_id.

    Lemma type_ptr_obj_repr_byte :
      forall  (ty : type) (p : ptr) (i sz : N),
        size_of σ ty = Some sz -> (* 1) [ty] has some byte-size [sz] *)
        (i < sz)%N ->             (* 2) by (1), [sz] is nonzero and [i] is a
                                        byte-offset into the object rooted at [p ,, o]

                                     NOTE: [forall ty, size_of (Tarray ty 0) = Some 0],
                                     but zero-length arrays are not permitted by the Standard
                                     (cf. <https://eel.is/c++draft/dcl.array#def:array,bound>).
                                     NOTE: if support for flexible array members is ever added,
                                     it will need to be carefully coordinated with these sorts
                                     of transport lemmas.
                                   *)
        (* 4) The existence of the "object representation" of an object of type [ty] -
           |  in conjunction with the premises - justifies "lowering" any
           |  [type_ptr ty p] fact to a collection of [type_ptr Tbyte (p ,, .[Tbyte ! i])]
           |  facts - where [i] is a byte-offset within the [ty] ([0 <= i < sizeof(ty)]).
           v *)
        type_ptr ty p |-- type_ptr Tbyte (p ,, (o_sub σ Tbyte i)).
    Proof.
      intros ty p i sz Hsz Hi. iIntros "#Htype".
      have Hbyte : size_of σ Tbyte = Some 1%N by done.
      iDestruct (type_ptr_subscript_valid ty p sz Tbyte 1 (Z.of_N i) pred.Strict
        Hsz Hbyte ltac:(lia) ltac:(intros _; right; lia) with "Htype") as "#Vi".
      iDestruct (type_ptr_subscript_valid ty p sz Tbyte 1 (Z.of_N i + 1) pred.Relaxed
        Hsz Hbyte ltac:(lia) ltac:(discriminate) with "Htype") as "Vend".
      iDestruct (strict_valid_ptr_nonnull_alloc_id with "Vi") as %(aid & Haid & Hneq).
      rewrite /type_ptr.
      iSplit.
      { iPureIntro. intros E. rewrite E ptr_alloc_id_nullptr in Haid.
        injection Haid as <-. contradiction. }
      iSplit.
      { iPureIntro. exists 1%N. split; [apply align_of_uchar|apply aligned_ptr_min]. }
      iSplit; first (iPureIntro; by exists 1%N).
      iFrame "Vi". rewrite -offset_ptr_dot o_dot_sub. iExact "Vend".
    Qed.

    Lemma type_ptr_obj_repr :
      forall (ty : type) (p : ptr) (sz : N),
        size_of σ ty = Some sz ->
        type_ptr ty p |-- [∗list] i ∈ seqN 0 sz, type_ptr Tbyte (p ,, o_sub σ Tbyte (Z.of_N i)).
    Proof.
      intros * Hsz; iIntros "#tptr".
      iApply big_sepL_intro; iIntros "!>" (k n) "%Hn'".
      assert (lookup (K:=N) (N.of_nat k) (seqN 0%N sz) = Some n)
        as Hn
        by (unfold lookupN, list_lookupN; rewrite Nat2N.id //);
        clear Hn'.
      apply lookupN_seqN in Hn as [? ?].
      iDestruct (type_ptr_obj_repr_byte ty p n sz Hsz ltac:(lia) with "tptr") as "$".
    Qed.

    (* [offset_congP] hoists [offset_cong] to [mpred] *)
    Definition offset_congP (σ : genv) (o1 o2 : offset) : mpred :=
      [| offset_cong σ o1 o2 |].

    (* [ptr_congP σ p1 p2] is an [mpred] which quotients [ptr_cong σ p1 p2]
       by requiring that [type_ptr Tbyte] holds for both [p1] /and/ [p2]. This property
       is intended to be sound and sufficient for transporting certain physical
       resources between [p1] and [p2] - and we hypothesize that it is also
       necessary.
     *)
    Definition ptr_congP (σ : genv) (p1 p2 : ptr) : mpred :=
      [| ptr_cong σ p1 p2 |] ** type_ptr Tbyte p1 ** type_ptr Tbyte p2.

    (* All [tptsto Tbyte] facts can be transported over [ptr_congP] [ptr]s.

       High level meaning:
       In the C++ object model, a single byte of storage can be accessed through different pointers,
       e.g. consider [struct C { int x; int y; } c;]. The first byte of the struct can be read through
       [static_cast<byte*>(&c)] (with pointer representation [c]) as well as [static_cast<byte*>(&c.x)]
       (with pointer representation [c ,, _field "::C" "x"]). To put an ownership discipline on this
       single byte, we build an equivalence relation on pointers that allows us to transport ownership
       of the byte between these different pointers. For example, half of the ownership could live at [c]
       and the other half of the ownership can live at [c ,, _field "::C" "x"].

       The standard justifies this as follows:
       1) (cf. [tptsto] comment) [tptsto ty q p v] ensures that [p] points to a memory
          location with C++ type [ty] and which has some value [v].
       2) (cf. [Section type_ptr_object_representation]) [type_ptr Tbyte] holds for all of the
          bytes (i.e. the "object reprsentation") constituting well-typed C++ objects.
       3) NOTE (JH): the following isn't quite true yet, but we'll want this when we flesh
          out [rawR]/[RAW_BYTES]:
          a) all values [v] can be converted into (potentially many) [raw_byte]s -
             which capture its "object representation"
          b) all [tptsto ty] facts can be shattered into (potentially many)
             [tptsto Tbyte _ _ (Vraw _)] facts corresponding to its "object representation"
       4) [tptsto Tbyte _ _ (Vraw _)] can be transported over [ptr_congP] [ptr]s:
          a) [tptso Tbyte _ _ (Vraw _)] facts deal with the "object representation" directly
             and thus permit erasing the structure of pointers in favor of reasoning about
             relative byte offsets from a shared [ptr]-prefix.
          b) the [ptr]s are [ptr_congP] so we know that:
             i) they share a common base pointer [p_base]
             ii) the byte-offset values of the C++ offsets which reconstitute the src/dst from
                 [p_base] are equal
             iii) NOTE: (cf. [valid_ptr_nonnull_nonzero]/[type_ptr_valid_ptr]/[type_ptr_nonnull] below)
                  [p_base] has some [vaddr], but we don't currently rely on this fact.
     *)
    (* TODO: improve our axiomatic support for raw values - including "shattering"
       non-raw values into their constituent raw pieces - to enable deriving
       [tptsto_ptr_congP_transport] from [tptsto_raw_ptr_congP_transport].
     *)
    Lemma tptsto_ptr_congP_transport : forall q p1 p2 v,
      ptr_congP σ p1 p2 |-- tptsto Tbyte q p1 v -* tptsto Tbyte q p2 v.
    Proof.
      iIntros (q p1 p2 v) "(%Hcong & #T1 & #T2)".
      iDestruct (type_ptr_strict_valid with "T1") as "V1".
      iDestruct (_valid_ptr_offset_defined with "V1") as %Hdef.
      have Ekey := storage_key_cong σ p1 p2 Hdef Hcong.
      rewrite /tptsto /mem_inj_own /oaddr_encodes /val_ /ghost_mem_own Ekey.
      iIntros "(%Hnn & %Hheap & %oa & _ & Mem & Enc & Hval)".
      iSplit; first (iDestruct "T2" as "[$ _]").
      iSplit; first done.
      iExists oa. iFrame "T2 Mem Enc Hval".
    Qed.

    Theorem tptsto_welltyped : forall p ty q (v : val),
      Observe (has_type_or_undef v ty) (tptsto ty q p v).
    Proof. intros. rewrite /tptsto. refine _. Qed.

    (* TODO: the [Notation] connects to the wrong definition *)
    #[local] Theorem tptsto_reference_to : forall p ty q (v : val),
      Observe (reference_to ty p) (tptsto ty q p v).
    Proof.
      intros. apply: observe_intro_persistent.
      iIntros "H".
      iDestruct (observe (type_ptr ty p) with "H") as
        "(%Hnn & %Hal & _ & #Hs & _)".
      rewrite /reference_to.
      iFrame (Hnn Hal).
      iSplit.
      { by iApply strict_valid_valid. }
      case_match; done.
    Qed.

  End with_cpp.

    Axiom struct_padding : forall `{!cpp_logic thread_info Σ} {σ:genv},
      ptr -> globname -> cQp.t -> mpred.

  Section with_cpp.
    Context `{cpp_logic}.

    #[global] Declare Instance struct_padding_timeless {σ:genv} :  Timeless3 struct_padding.
    #[global] Declare Instance struct_padding_fractional : forall {σ : genv} p cls, CFractional (struct_padding p cls).
    #[global] Declare Instance struct_padding_frac_valid :  forall {σ : genv} p cls, CFracValid0 (struct_padding p cls).

    #[global] Declare Instance struct_padding_type_ptr_observe : forall {σ : genv} p cls q, Observe (type_ptr (Tnamed cls) p) (struct_padding p cls q).

  End with_cpp.

    Axiom union_padding : forall `{!cpp_logic thread_info Σ} {σ:genv},
      ptr -> globname -> cQp.t -> option nat -> mpred.

  Section with_cpp.
    Context `{cpp_logic}.

    #[global] Declare Instance union_padding_timeless {σ:genv} :  Timeless4 union_padding.
    #[global] Declare Instance union_padding_fractional : forall {σ : genv} p cls, CFractional1 (union_padding p cls).
    #[global] Declare Instance union_padding_frac_valid :  forall {σ : genv} p cls, CFracValid1 (union_padding p cls).

    #[global] Declare Instance union_padding_type_ptr_observe : forall {σ : genv} p cls q active,
        Observe (type_ptr (Tnamed cls) p) (union_padding p cls q active).
    #[global] Declare Instance union_padding_agree : forall {σ : genv} p cls q q' i i',
        Observe2 [| i = i' |] (union_padding p cls q i) (union_padding p cls q' i').

  End with_cpp.

  #[global] Instance tptsto_params : Params (@tptsto) 3 := {}.

End SimpleCPP.

Module Type SimpleCPP_INTF := CPP_LOGIC_CLASS <+ CPP_LOGIC PTRS_IMPL VALUES_DEFS_IMPL.
Module L <: SimpleCPP_INTF := SimpleCPP.

Module VALID_PTR : VALID_PTR_AXIOMS PTRS_IMPL VALUES_DEFS_IMPL L L.
  Import SimpleCPP.

  Notation strict_valid_ptr := (_valid_ptr Strict).
  Notation valid_ptr := (_valid_ptr Relaxed).
  Section with_cpp.
    Context `{cpp_logic} {σ : genv}.

    Lemma invalid_ptr_invalid vt :
      _valid_ptr vt invalid_ptr |-- False.
    Proof.
      iIntros "H". iDestruct (_valid_ptr_alloc_id with "H") as %Haid.
      destruct Haid as [aid Haid]. discriminate.
    Qed.

    (** Justified by [https://eel.is/c++draft/expr.add#4.1]. *)
    Lemma _valid_ptr_nullptr_sub_false : forall vt ty (i : Z) (_ : i <> 0),
      _valid_ptr vt (nullptr ,, o_sub σ ty i) |-- False.
    Proof.
      intros vt ty i Hnz. iIntros "H".
      iDestruct (_valid_ptr_cases (resolve:=σ) with "H") as %Hcases.
      destruct Hcases as [Heq|[(aid & Haid & Hnn) _]].
      - rewrite _dot.unlock /DOT_dot /= in Heq.
        apply (f_equal (fun p => match p with
          | invalid_ptr_ => []
          | offset_ptr _ o => `o
          end)) in Heq.
        rewrite /= /raw_offset_merge /o_sub in Heq.
        move: Heq. case_decide; first contradiction.
        rewrite /= /mkOffset /mk_offset_seg /= /simple_pointers_utils.o_sub_off.
        destruct (size_of σ (erase_qualifiers ty)); simpl.
        + repeat case_decide; try discriminate; naive_solver.
        + discriminate.
      - have Hroot := ptr_alloc_id_offset (p:=nullptr) (o:=o_sub σ ty i)
          (ex_intro _ aid Haid).
        rewrite ptr_alloc_id_nullptr Haid in Hroot.
        injection Hroot as ->. contradiction.
    Qed.

    (*
    TODO Controversial; if [f] is the first field, [nullptr->f] or casts relying on
    https://eel.is/c++draft/basic.compound#4 might invalidate this.
    To make this valid, we could ensure our axiomatic semantics produces
    [nullptr] instead of [nullptr ., o_field]. *)
    (* Axiom _valid_ptr_nullptr_field_false : forall vt f,
      _valid_ptr vt (nullptr ,, o_field σ f) |-- False. *)

    (** These axioms are named after the predicate in the conclusion. *)



    Lemma _valid_ptr_sub (i j k : Z) (p : ptr) ty vt1 vt2 vt :
      (i <= j < k)%Z ->
      (vt = pred.Strict -> exists sz, size_of σ ty = Some sz /\ (0 < sz)%N) ->
      _valid_ptr vt1 (p ,, o_sub σ ty i) ⊢
      _valid_ptr vt2 (p ,, o_sub σ ty k) -∗ _valid_ptr vt (p ,, o_sub σ ty j).
    Proof. apply SimpleCPP._valid_ptr_sub. Qed.

    Lemma strict_valid_ptr_sub : ∀ (i j k : Z) p ty vt1 vt2,
      (i <= j < k)%Z ->
      (exists sz, size_of σ ty = Some sz /\ (0 < sz)%N) ->
      _valid_ptr vt1 (p ,, o_sub σ ty i) |--
      _valid_ptr vt2 (p ,, o_sub σ ty k) -* strict_valid_ptr (p ,, o_sub σ ty j).
    Proof. apply SimpleCPP.strict_valid_ptr_sub_guarded. Qed.

    (** A nonzero subscript after a field cannot erase the field prefix.
        Every proper prefix is strictly within the allocation range, even when
        the subscript's element size is zero. *)
    Lemma strict_valid_ptr_field_sub : ∀ p ty (i : Z) f vt,
      (0 < i)%Z ->
      _valid_ptr vt (p ,, o_field σ f ,, o_sub σ ty i) |-- strict_valid_ptr (p ,, o_field σ f).
    Proof.
      intros p ty i f vt Hi. have Hnz : i <> 0%Z by lia.
      iIntros "H". iDestruct (_valid_ptr_offset_defined with "H") as %Hdefined.
      apply (ptr_offset_defined_dot σ) in Hdefined as [Hpf Hsub].
      apply (ptr_offset_defined_dot σ) in Hpf as [Hp Hf].
      have [z Hz] := eval_o_field_defined σ f Hf.
      have [sz Hsz] := eval_o_sub_defined σ ty i Hsub.
      destruct p as [|root off]; first contradiction.
      have Hraw := offset_field_sub_raw σ off f z ty i sz Hp Hz Hsz Hnz.
      rewrite _dot.unlock /DOT_dot /= in Hraw.
      rewrite /_valid_ptr. iDestruct "H" as "[[%Hnull _]|H]".
      { exfalso. exact (field_sub_ptr_ne_null σ (offset_ptr root off) f ty i Hnz Hnull). }
      rewrite _dot.unlock /DOT_dot /=.
      iDestruct "H" as (l h) "(B & %Haid & %Hpath)".
      iRight. iExists l, h. iFrame "B". iSplit; first done.
      iPureIntro. rewrite Hraw in Hpath.
      apply (raw_path_valid_strict_prefix vt root l h _
        [(o_sub_ (erase_qualifiers ty) i, Z.of_N sz * i)%Z]);
        [discriminate|exact Hpath].
    Qed.

    (* TODO: can we deduce that [p] is strictly valid? *)
    Lemma _valid_ptr_field : ∀ p f vt,
      _valid_ptr vt (p ,, o_field σ f) |-- _valid_ptr vt p.
    Proof.
      intros p f vt. iIntros "H".
      iDestruct (_valid_ptr_offset_defined with "H") as %Hdefined.
      apply (ptr_offset_defined_dot σ) in Hdefined as [Hp Hf].
      have [z Hz] := eval_o_field_defined σ f Hf.
      rewrite /_valid_ptr. iDestruct "H" as "[[%Hnull _]|H]".
      { exfalso. exact (field_ptr_ne_null σ p f Hnull). }
      destruct p as [|root off]; first contradiction.
      rewrite _dot.unlock /DOT_dot /=.
      iDestruct "H" as (l h) "(B & %Haid & %Hpath)".
      iRight. iExists l, h. iFrame "B". iSplit; first done.
      iPureIntro.
      have Hraw := offset_field_raw σ off f z Hp Hz.
      rewrite _dot.unlock /DOT_dot /= in Hraw.
      rewrite Hraw in Hpath.
      exact (raw_path_valid_prefix _ _ _ _ _ _ Hpath).
    Qed.
    (* TODO: Pointers to fields can't be past-the-end, right?
    Except 0-size arrays. *)
    (* Axiom strict_valid_ptr_field : ∀ p f,
      valid_ptr (p ,, o_field σ f) |--
      strict_valid_ptr (p ,, o_field σ f). *)
    (* TODO: if we add [strict_valid_ptr_field], we can derive
    [_valid_ptr_field] from just [strict_valid_ptr_field] *)
    (* Axiom strict_valid_ptr_field : ∀ p f,
      strict_valid_ptr (p ,, o_field σ f) |-- strict_valid_ptr p. *)

    Lemma valid_o_sub_size : forall p ty i vt,
      _valid_ptr vt (p ,, o_sub σ ty i) |-- [| is_Some (size_of σ ty) |].
    Proof.
      intros p ty i vt. iIntros "H".
      iDestruct (_valid_ptr_offset_defined with "H") as %Hpath.
      iPureIntro. apply (ptr_offset_defined_dot σ) in Hpath as [_ Hsub].
      exact (eval_o_sub_defined σ ty i Hsub).
    Qed.



    Axiom type_ptr_o_base : forall derived base p,
      class_derives derived [base] ->
      base_layout_compatible σ derived base ->
      type_ptr (Tnamed derived) p ⊢ type_ptr (Tnamed base) (p ,, _base derived base).



    Axiom type_ptr_o_field_type_ptr : forall p fld cls (st : Struct),
      glob_def σ cls = Some (Gstruct st) ->
      fld ∈ s_fields st →
      type_ptr (Tnamed cls) p ⊢ type_ptr fld.(mem_type) (p .,
        Field cls fld.(mem_name)).

    Lemma type_ptr_o_sub : forall p (m n : N) ty,
      (m < n)%N ->
      type_ptr (Tarray ty n) p ⊢ type_ptr ty (p ,, _sub ty m).
    Proof.
      intros p m n ty Hmn. iIntros "#T".
      iDestruct (type_ptr_size with "T") as %(total & Htotal).
      destruct (proj1 (size_of_array_shatter ty n total) Htotal)
        as (esz & -> & Hes & Harray).
      iDestruct (type_ptr_subscript_valid (Tarray ty n) p (n*esz)%N ty esz
        (Z.of_N m) pred.Strict Harray Hes ltac:(rewrite N2Z.inj_mul; nia)
        ltac:(intros _; destruct (decide (esz=0%N));
          [left; subst; lia|right; rewrite N2Z.inj_mul; nia]) with "T") as "#Vi".
      iDestruct (type_ptr_subscript_valid (Tarray ty n) p (n*esz)%N ty esz
        (Z.of_N m+1) pred.Relaxed Harray Hes ltac:(rewrite N2Z.inj_mul; nia)
        ltac:(discriminate) with "T") as "Vend".
      iDestruct (type_ptr_aligned_pure with "T") as %Hal.
      rewrite /aligned_ptr_ty align_of_array in Hal.
      iDestruct (type_ptr_strict_valid with "T") as "V0".
      iDestruct (_valid_ptr_vaddr (resolve:=σ) with "V0") as %Hva.
      have Hal' := aligned_ptr_ty_subscript σ p ty esz (Z.of_N m) Hes Hal Hva.
      iDestruct (strict_valid_ptr_nonnull_alloc_id with "Vi") as %(aid & Haid & Hneq).
      rewrite /type_ptr. iSplit.
      { iPureIntro. intros E. rewrite E ptr_alloc_id_nullptr in Haid.
        injection Haid as <-. contradiction. }
      iSplit; first done.
      iSplit; first (iPureIntro; by exists esz).
      iFrame "Vi". rewrite -offset_ptr_dot o_dot_sub. iExact "Vend".
    Qed.

    Lemma type_ptr_o_sub_end : forall p (n : N) ty,
      type_ptr (Tarray ty n) p ⊢ valid_ptr (p ,, _sub ty n).
    Proof.
      intros p n ty. iIntros "T".
      iDestruct (type_ptr_size with "T") as %(total & Htotal).
      destruct (proj1 (size_of_array_shatter ty n total) Htotal)
        as (esz & -> & Hes & Harray).
      iApply (type_ptr_subscript_valid (Tarray ty n) p (n*esz)%N ty esz
        (Z.of_N n) pred.Relaxed Harray Hes ltac:(rewrite N2Z.inj_mul; nia)
        ltac:(discriminate) with "T").
    Qed.

    Lemma o_base_directly_derives : forall p base derived,
      strict_valid_ptr (p ,, o_base σ derived base) |--
      [| directly_derives σ derived base |].
    Proof.
      intros p base derived. iIntros "H".
      iDestruct (_valid_ptr_offset_defined with "H") as %Hpath.
      iPureIntro. apply (ptr_offset_defined_dot σ) in Hpath as [_ Hbase].
      rewrite /eval_offset /eval_raw_offset /= /mk_offset_seg /=
        /simple_pointers_utils.o_base_off in Hbase.
      destruct (parent_offset σ derived base); naive_solver.
    Qed.

    Lemma o_derived_directly_derives : forall p base derived,
      strict_valid_ptr (p ,, o_derived σ base derived) |--
      [| directly_derives σ derived base |].
    Proof.
      intros p base derived. iIntros "H".
      iDestruct (_valid_ptr_offset_defined with "H") as %Hpath.
      iPureIntro. apply (ptr_offset_defined_dot σ) in Hpath as [_ Hbase].
      rewrite /eval_offset /eval_raw_offset /= /mk_offset_seg /=
        /simple_pointers_utils.o_derived_off in Hbase.
      destruct (parent_offset σ derived base); naive_solver.
    Qed.

  End with_cpp.
End VALID_PTR.
