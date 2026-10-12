Require Import iris.bi.monpred.
Require Import iris.base_logic.lib.iprop.
Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.notations.
Require Import skylabs.lang.cpp.code_notations.
Require Import skylabs.lang.cpp.semantics.genv.
Require Import skylabs.lang.cpp.semantics.types.
Require Import skylabs.lang.cpp.semantics.subtyping.
Require Import skylabs.lang.cpp.model.simple_pointers_utils.
Require Import skylabs.lang.cpp.model.inductive_pointers_utils.
Require Import skylabs.lang.cpp.model.inductive_pointers.
Require Import skylabs.lang.cpp.model.simple_pred.
Require Import skylabs.iris.extra.proofmode.proofmode.
Import PTRS_IMPL VALUES_DEFS_IMPL SimpleCPP address_sums BaseLayoutChecks.
Set Default Proof Using "Type*".

Definition bad_base_struct : Struct :=
  Build_Struct [] [] [] [] "Base::~Base()"%cpp_name true None POD 1 1.
Definition bad_derived_struct : Struct :=
  Build_Struct [("Base"%cpp_name, {| li_offset := 16 |})]
    [] [] [] "Derived::~Derived()"%cpp_name true None POD 1 1.
Definition bad_base_env : genv :=
  {| genv_tu := makeTranslationUnit ∅
       {[ "Base"%cpp_name := Gstruct bad_base_struct;
          "Derived"%cpp_name := Gstruct bad_derived_struct ]}
       ∅ [] [] abi.abi_default ∅ ∅ ∅ ∅;
     member_pointer_bitsize := bitsize.W64 |}.

Lemma bad_base_derives : @class_derives bad_base_env "Derived" ["Base"%cpp_name].
Proof.
  refine (@Derives_base bad_base_env "Derived" "Base" bad_derived_struct {| li_offset := 16 |} [] _ _ _).
  - vm_compute. reflexivity.
  - by left.
  - apply (@Derives_here bad_base_env "Base" bad_base_struct).
    vm_compute. reflexivity.
Qed.
Lemma bad_base_offset : parent_offset bad_base_env "Derived" "Base" = Some 2%Z.
Proof. rewrite parent_offset.unlock. vm_compute. reflexivity. Qed.
Lemma bad_derived_size : size_of bad_base_env "Derived"%cpp_type = Some 1%N.
Proof. vm_compute. reflexivity. Qed.
Lemma bad_derived_align : @align_of bad_base_env "Derived"%cpp_type = Some 1%N.
Proof. apply align_of_named. vm_compute. reflexivity. Qed.

Section concrete_model.
  Context {thread_info : biIndex} {Σ : gFunctors}
    {Hlogic : SimpleCPP.cpp_logic thread_info Σ}.
  #[local] Existing Instance Hlogic.
  Let σ : genv := bad_base_env.
  #[local] Existing Instance σ.

  Lemma bad_derived_typed aid :
    aid <> null_alloc_id -> blocks_own (alloc_ptr aid 8) 0 1 ⊢
    type_ptr "Derived"%cpp_type (alloc_ptr aid 8).
  Proof.
    intros Haid. iIntros "#B". rewrite /type_ptr.
    iSplit.
    { iPureIntro. intros E. apply (f_equal ptr_alloc_id) in E.
      simpl in E. injection E as E. contradiction. }
    iSplit.
    { iPureIntro. exists 1%N. split; [apply bad_derived_align|apply aligned_ptr_min]. }
    iSplit; first (iPureIntro; exists 1%N; apply bad_derived_size).
    rewrite /_valid_ptr _dot.unlock /DOT_dot /=.
    have Hroot : raw_path_valid pred.Strict (alloc_ptr_ aid 8) 0 1 [].
    { apply (raw_path_valid_nil _ _ _ _ 8%N); try done. left; lia. }
    iSplit.
    - iRight. iExists 0%Z, 1%Z. iFrame "B".
      iSplit; first (iPureIntro; exists aid; split; done).
      iPureIntro. exact Hroot.
    - iRight. iExists 0%Z, 1%Z. iFrame "B".
      iSplit; first (iPureIntro; exists aid; split; done).
      iPureIntro.
      change (raw_path_valid pred.Relaxed (alloc_ptr_ aid 8) 0 1
        ([] ++ [(o_sub_ "Derived"%cpp_type 1,1%Z)])).
      apply (raw_path_valid_snoc _ _ _ _ _ _ 1%Z 9%N); try done.
      right; done.
  Qed.

  Lemma bad_base_not_strict aid :
    blocks_own (alloc_ptr aid 8) 0 1 ⊢
    _valid_ptr pred.Strict (alloc_ptr aid 8 ,, o_base σ "Derived" "Base") -∗ False.
  Proof.
    iIntros "B V". rewrite /_valid_ptr.
    iDestruct "V" as "[[_ %Hvt]|V]"; first discriminate.
    rewrite _dot.unlock /DOT_dot /=.
    iDestruct "V" as (l h) "(B' & _ & %Hpath)".
    iDestruct (blocks_own_range_agree with "[$B $B']") as %E.

    injection E as <- <-.
    rewrite /o_base /mkOffset /mk_offset_seg /= /o_base_off /σ bad_base_offset /= in Hpath.
    change (raw_path_valid pred.Strict (alloc_ptr_ aid 8) 0 1
      [(o_base_ "Derived" "Base",2%Z)]) in Hpath.
    destruct (raw_path_valid_end _ _ _ _ _ Hpath) as (z & va & Hz & _ & _ & Hr).
    change (Some 2%Z = Some z) in Hz. injection Hz as <-.
    destruct Hr as [Hr|[Hbad _]]; [lia|discriminate].
  Qed.

  Lemma old_base_rule_refuted
      (old_rule : forall derived base p,
        class_derives derived [base] ->
        type_ptr (Tnamed derived) p ⊢ type_ptr (Tnamed base) (p ,, o_base σ derived base)) aid :
    aid <> null_alloc_id -> blocks_own (alloc_ptr aid 8) 0 1 ⊢ False.
  Proof.
    intros Haid. iIntros "#B".
    iDestruct (bad_derived_typed aid Haid with "B") as "T".
    iDestruct (old_rule _ _ _ bad_base_derives with "T") as "TB".
    iDestruct (type_ptr_strict_valid with "TB") as "V".
    by iApply (bad_base_not_strict with "B V").
  Qed.
End concrete_model.

(** Computed layout guards reject bad metadata before pointer typing. *)
Example bad_base_guard_rejected :
  tu_base_layout_compatible bad_base_env.(genv_tu) "Derived" "Base" = false.
Proof. vm_compute. reflexivity. Qed.

Definition base_fixture_env (z : Z) (dsz dal bsz bal : N) : genv :=
  {| genv_tu := makeTranslationUnit ∅
       {[ "Base"%cpp_name := Gstruct
          (Build_Struct [] [] [] [] "Base::~Base()"%cpp_name true None POD bsz bal);
          "Derived"%cpp_name := Gstruct
          (Build_Struct [("Base"%cpp_name, {| li_offset := 8*z |})]
            [] [] [] "Derived::~Derived()"%cpp_name true None POD dsz dal) ]}
       ∅ [] [] abi.abi_default ∅ ∅ ∅ ∅;
     member_pointer_bitsize := bitsize.W64 |}.

Definition ordinary_base_env : genv := base_fixture_env 2 4 1 1 1.

Example ordinary_base_guard :
  tu_base_layout_compatible ordinary_base_env.(genv_tu) "Derived" "Base" = true.
Proof. vm_compute. reflexivity. Qed.
Example zero_offset_base_guard :
  tu_base_layout_compatible (base_fixture_env 0 1 1 1 1).(genv_tu) "Derived" "Base" = true.
Proof. vm_compute. reflexivity. Qed.
Example negative_base_guard_rejected :
  tu_base_layout_compatible (base_fixture_env (-1) 4 1 1 1).(genv_tu) "Derived" "Base" = false.
Proof. vm_compute. reflexivity. Qed.
Example base_alignment_guard_rejected :
  tu_base_layout_compatible (base_fixture_env 1 4 2 2 2).(genv_tu) "Derived" "Base" = false.
Proof. vm_compute. reflexivity. Qed.
Example base_extent_guard_rejected :
  tu_base_layout_compatible (base_fixture_env 3 4 1 2 1).(genv_tu) "Derived" "Base" = false.
Proof. vm_compute. reflexivity. Qed.
Example boundary_base_guard_rejected :
  tu_base_layout_compatible (base_fixture_env 4 4 1 0 1).(genv_tu) "Derived" "Base" = false.
Proof. vm_compute. reflexivity. Qed.
Example zero_sized_base_guard :
  tu_base_layout_compatible (base_fixture_env 0 0 1 0 1).(genv_tu) "Derived" "Base" = true.
Proof. vm_compute. reflexivity. Qed.

#[local] Instance ordinary_base_compat : ordinary_base_env.(genv_tu) ⊧ ordinary_base_env.
Proof. constructor. reflexivity. Qed.
Lemma ordinary_base_derives : @class_derives ordinary_base_env "Derived" ["Base"%cpp_name].
Proof.
  apply (tu_class_derives_sound ordinary_base_env.(genv_tu)).

  vm_compute. exact I.
Qed.
Lemma ordinary_base_layout : base_layout_compatible ordinary_base_env "Derived" "Base".
Proof. exact (tu_base_layout_compatible_sound _ _ ordinary_base_guard). Qed.

Section ordinary_base_model.
  Context {thread_info : biIndex} {Σ : gFunctors}
    {Hlogic : SimpleCPP.cpp_logic thread_info Σ}.
  #[local] Existing Instance Hlogic.
  Let σ : genv := ordinary_base_env.
  #[local] Existing Instance σ.

  (** Starting at the base address, move back to the derived object. The
      guarded upcast below cancels that path completely. *)
  Lemma derived_backwards_typed aid :
    aid <> null_alloc_id -> blocks_own (alloc_ptr aid 8) (-2) 2 ⊢
    type_ptr "Derived"%cpp_type (alloc_ptr aid 8 ,, o_derived σ "Base" "Derived").
  Proof.
    intros Haid. iIntros "#B". rewrite /type_ptr.
    iSplit.
    { iPureIntro. intros E. apply (f_equal ptr_alloc_id) in E.
      rewrite _dot.unlock /DOT_dot /= in E. injection E as E. contradiction. }
    iSplit.
    { iPureIntro. exists 1%N. split; last apply aligned_ptr_min.
      apply align_of_named. vm_compute. reflexivity. }
    iSplit; first (iPureIntro; exists 4%N; vm_compute; reflexivity).
    rewrite /_valid_ptr _dot.unlock /DOT_dot /=.
    have Hz : parent_offset σ "Derived" "Base" = Some 2%Z.
    { rewrite parent_offset.unlock. vm_compute. reflexivity. }
    have Hroot : raw_path_valid pred.Strict (alloc_ptr_ aid 8) (-2) 2 [].
    { apply (raw_path_valid_nil _ _ _ _ 8%N); try done. left; lia. }
    have Hderived : raw_path_valid pred.Strict (alloc_ptr_ aid 8) (-2) 2
      [(o_derived_ "Base" "Derived",(-2)%Z)].
    { change (raw_path_valid pred.Strict (alloc_ptr_ aid 8) (-2) 2
        ([] ++ [(o_derived_ "Base" "Derived",(-2)%Z)])).
      apply (raw_path_valid_snoc _ _ _ _ _ _ (-2)%Z 6%N); try done. left; lia. }
    iSplit.
    - iRight. iExists (-2)%Z,2%Z. iFrame "B".
      iSplit; first (iPureIntro; exists aid; split; done).
      iPureIntro. rewrite /o_derived /mkOffset /mk_offset_seg /= /o_derived_off Hz /=.
      exact Hderived.
    - iRight. iExists (-2)%Z,2%Z. iFrame "B".
      iSplit; first (iPureIntro; exists aid; split; done).
      iPureIntro. rewrite /o_derived /mkOffset /mk_offset_seg /= /o_derived_off Hz /=.
      change (raw_path_valid pred.Relaxed (alloc_ptr_ aid 8) (-2) 2
        ([(o_derived_ "Base" "Derived",(-2)%Z)] ++ [(o_sub_ "Derived"%cpp_type 1,4%Z)])).
      apply (raw_path_valid_snoc _ _ _ _ _ _ 2%Z 10%N); try done. right; done.
  Qed.

  Lemma checked_base_cancels aid :
    aid <> null_alloc_id -> blocks_own (alloc_ptr aid 8) (-2) 2 ⊢
    type_ptr "Base"%cpp_type (alloc_ptr aid 8).
  Proof.
    intros Haid. iIntros "B".
    iDestruct (derived_backwards_typed aid Haid with "B") as "T".
    have Hrule : type_ptr "Derived"%cpp_type (alloc_ptr aid 8 ,, o_derived σ "Base" "Derived") ⊢
      type_ptr "Base"%cpp_type (alloc_ptr aid 8 ,, o_derived σ "Base" "Derived" ,, o_base σ "Derived" "Base") :=
      SimpleCPP.type_ptr_o_base_guarded _ _ _ ordinary_base_derives ordinary_base_layout.
    rewrite (o_derived_base σ (alloc_ptr aid 8) "Base" "Derived") in Hrule.
    - by iApply Hrule.
    - exists 2%Z. rewrite parent_offset.unlock. vm_compute. reflexivity.
  Qed.

  Lemma checked_base_one_past aid :
    aid <> null_alloc_id -> blocks_own (alloc_ptr aid 8) (-2) 2 ⊢
    _valid_ptr pred.Relaxed (alloc_ptr aid 8 ,, o_sub σ "Base"%cpp_type 1).
  Proof.
    intros Haid. iIntros "B".
    iDestruct (checked_base_cancels aid Haid with "B") as "T".
    by iApply (type_ptr_valid_plus_one with "T").
  Qed.
  Lemma ordinary_derived_typed aid :
    aid <> null_alloc_id -> blocks_own (alloc_ptr aid 8) 0 4 ⊢
    type_ptr "Derived"%cpp_type (alloc_ptr aid 8).
  Proof.
    intros Haid. iIntros "#B". rewrite /type_ptr.
    iSplit.
    { iPureIntro. intros E. apply (f_equal ptr_alloc_id) in E.
      simpl in E. injection E as E. contradiction. }
    iSplit.
    { iPureIntro. exists 1%N. split; last apply aligned_ptr_min.
      apply align_of_named. vm_compute. reflexivity. }
    iSplit; first (iPureIntro; exists 4%N; vm_compute; reflexivity).
    rewrite /_valid_ptr _dot.unlock /DOT_dot /=.
    have Hroot : raw_path_valid pred.Strict (alloc_ptr_ aid 8) 0 4 [].
    { apply (raw_path_valid_nil _ _ _ _ 8%N); try done. left; lia. }
    iSplit.
    - iRight. iExists 0%Z,4%Z. iFrame "B".
      iSplit; first (iPureIntro; exists aid; split; done).
      iPureIntro. exact Hroot.
    - iRight. iExists 0%Z,4%Z. iFrame "B".
      iSplit; first (iPureIntro; exists aid; split; done).
      iPureIntro.
      change (raw_path_valid pred.Relaxed (alloc_ptr_ aid 8) 0 4
        ([] ++ [(o_sub_ "Derived"%cpp_type 1,4%Z)])).
      apply (raw_path_valid_snoc _ _ _ _ _ _ 4%Z 12%N); try done. right; done.
  Qed.

  Lemma checked_nonzero_base aid :
    aid <> null_alloc_id -> blocks_own (alloc_ptr aid 8) 0 4 ⊢
    type_ptr "Base"%cpp_type (alloc_ptr aid 8 ,, o_base σ "Derived" "Base").
  Proof.
    intros Haid. iIntros "B".
    iDestruct (ordinary_derived_typed aid Haid with "B") as "T".
    by iApply (SimpleCPP.type_ptr_o_base_guarded _ _ _ ordinary_base_derives ordinary_base_layout with "T").
  Qed.

End ordinary_base_model.
