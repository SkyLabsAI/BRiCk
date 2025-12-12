(*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import iris.algebra.excl.
Require Import iris.algebra.gmap.
Require Import iris.algebra.lib.frac_auth.
Require Import iris.bi.monpred.
Require Import iris.bi.lib.fractional.
Require Import bluerock.iris.extra.proofmode.proofmode.

Require Import bluerock.iris.extra.bi.fractional.
Require Import bluerock.iris.extra.bi.cancelable_invariants.
Require Import bluerock.lang.cpp.bi.cfractional.
Require Import bluerock.iris.extra.base_logic.own_instances.

Require Import bluerock.prelude.base.
Require Import bluerock.prelude.option.
Require Import bluerock.prelude.arith.z_to_bytes.
Require Import bluerock.lang.cpp.algebra.cfrac.
Require Import bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.semantics.
Require Import bluerock.lang.cpp.logic.mpred.
Require Import bluerock.lang.cpp.logic.pred.

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
    `{!BiEmbed siPropI PROP} `{!HasOwnValid PROP (gmapR K (cfractionalR V))}
    v1 v2 γ q1 q2 k :
    Observe2 [| v1 = v2 |] (gmap_own γ q1 k v1) (gmap_own γ q2 k v2).
  Proof.
    apply: observe_2_intro_only_provable.
    apply bi.wand_intro_r; rewrite /gmap_own -own_op singleton_op.
    rewrite own_valid discrete_valid singleton_valid.
    by iIntros "!%" => /cfrac_valid [].
  Qed.

  (**
  We keep this instance local because guarding it with [CFracValid2]
  prevents it from firing. (Perhaps due to the let binding.)
  *)
  Instance gmap_own_cfrac_valid γ
    `{!BiEmbed siPropI PROP} `{!HasOwnValid PROP (gmapR K (cfractionalR V))} :
    ∀ q k v, Observe [| cQp.frac q ≤ 1 |]%Qp (gmap_own γ q k v).
  Proof.
    intros. apply: observe_intro_only_provable.
    rewrite /gmap_own own_valid !discrete_valid singleton_valid.
    by iIntros "!%" => /pair_valid [? _].
  Qed.
End fractional.
#[local] Existing Instance gmap_own_cfrac_valid.

Require Import bluerock.lang.cpp.model.inductive_pointers.
(* Stand-in for actual models.
Ensures that everything needed is properly functorized. *)
Import PTRS_IMPL.
Declare Module Import VALUES_DEFS_IMPL : VALUES_INTF_FUNCTOR PTRS_IMPL.

Implicit Types (p : ptr).

(** A consistency proof for [CPP_LOGIC_CLASS] *)
Module SimpleCPP_BASE <: CPP_LOGIC_CLASS.

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
    ; ghost_memG : inG Σ (gmapR ptr (cfractionalR val))
      (* ^ this represents the contents of the C++ runtime that might
         not be represented in physical memory, e.g. values stored in
         registers or temporaries on the stack *)
    ; mem_injG : inG Σ (gmapUR ptr (agreeR (leibnizO (option addr))))
      (* ^ this carries the (compiler-supplied) mapping from C++ locations
         (represented as pointers) to physical memory addresses. Locations that
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
      own (A := gmapR ptr (cfractionalR val))
        cpp_ghost.(ghost_mem_name) {[ p := cfrac q v ]}.
    Definition mem_inj_own (p : ptr) (va : option N) : mpred :=
      own (A := gmapUR ptr (agreeR (leibnizO (option addr))))
        cpp_ghost.(mem_inj_name) {[ p := to_agree va ]}.
    Definition blocks_own (p : ptr) (l h : Z) : mpred :=
      own (A := gmapUR ptr (agreeR (leibnizO (Z * Z))))
        cpp_ghost.(blocks_name) {[ p := to_agree (l, h) ]}.
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

    Definition _valid_ptr vt (p : ptr) : mpred :=
      [| p = nullptr /\ vt = Relaxed |] \\//
        Exists σ' base l h o zo,
                blocks_own base l h **
                in_range vt l zo h **
                [| eval_offset σ' o = Some zo /\ p = base ,, o |] **
                [| ptr_vaddr p <> Some 0%N |].
    (* strict validity (not past-the-end) *)
    Notation strict_valid_ptr := (_valid_ptr Strict).
    (* relaxed validity (past-the-end allowed) *)
    Notation valid_ptr := (_valid_ptr Relaxed).

    Instance _valid_ptr_persistent : forall b p, Persistent (_valid_ptr b p) := _.
    Instance _valid_ptr_affine : forall b p, Affine (_valid_ptr b p) := _.
    Instance _valid_ptr_timeless : forall b p, Timeless (_valid_ptr b p) := _.

    (* Needs validity to exclude non-null pointers with 0 addresses but
    non-null provenance (which can be created by pointer arithmetic!) as
    invalid. *)
    Lemma same_address_eq_null p tv :
      _valid_ptr tv p |--
      [| same_address p nullptr <-> p = nullptr |].
    Proof.
      rewrite /_valid_ptr same_address_eq; iIntros "[[-> _]|H]";
        [ |iDestruct "H" as (??????) "(_ & _ & _ & %Hne)"]; iIntros "!%".
      by rewrite same_property_iff ptr_vaddr_nullptr; naive_solver.
      rewrite same_property_iff; split; last intros ->;
        rewrite ptr_vaddr_nullptr; naive_solver.
    Qed.

    Theorem valid_ptr_nullptr : |-- valid_ptr nullptr.
    Proof. by iLeft. Qed.

    Theorem not_strictly_valid_ptr_nullptr : strict_valid_ptr nullptr |-- False.
    Proof.
      iDestruct 1 as "[[_ %]|H] /="; first done.
      by iDestruct "H" as (??????) "(_ & _ & _ & %Hne)".
    Qed.
    Typeclasses Opaque _valid_ptr.

    Lemma strict_valid_valid p :
      strict_valid_ptr p |-- valid_ptr p.
    Proof.
      rewrite /_valid_ptr/=; f_equiv. { by iIntros "!%" ([_ ?]). }
      by setoid_rewrite in_range_weaken.
    Qed.

    Axiom valid_ptr_alloc_id : forall p,
      valid_ptr p |-- [| is_Some (ptr_alloc_id p) |].
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
        | Tchar_ ct => False (* TODO *)
        | Tmember_pointer _ _ =>
          match v with
          | Vint v =>
            (* note: this is really an offset *)
            in_Z_to_bytes_bounds POINTER_BITSZ Unsigned v /\
            vs = Z_to_bytes POINTER_BITSZ Unsigned v
          | Vundef => pure_encodes_undef POINTER_BITSZ vs
          | _ => False
          end
        | Tbool =>
          if decide (v = Vint 0) then vs = [Rval 0%N]
          else if decide (v = Vint 1) then vs = [Rval 1%N]
          else False
        | Tnullptr =>
          vs = cptr 0 /\ v = Vptr nullptr
        | Tfloat_ _ => False
        | Tarch _ _ => False
        | Tptr _ =>
          match v with
          | Vptr p =>
            if decide (p = nullptr) then
              vs = cptr 0
            else
              vs = aptr p
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

                      | Tmember_pointer _ _ | Tnullptr | Tptr _
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
        by destruct sz.
        erewrite length_pure_encodes_undef; eauto. by destruct sz.
      Qed.

      Lemma length_encodes_pos t v vs :
        pure_encodes t v vs ->
        length vs > 0.
      Proof.
        move=> /length_encodes ->. have ?: 1 > 0 by exact: le_n.
        induction t; simpl; try solve [ lia | exact: bytesNat_pos ].
        destruct sz; compute; lia.
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
      rewrite own_valid discrete_valid singleton_valid.
      by iIntros "!%" => /= /to_agree_op_inv_L.
    Qed.

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
    Admitted.

    Lemma type_ptr_strict_valid ty p :
      type_ptr ty p |-- strict_valid_ptr p.
    Proof. iDestruct 1 as "(_ & _ & _ & $ & _)". Qed.

    Lemma type_ptr_valid_plus_one ty p :
      (* size_of resolve ty = Some sz -> *)
      type_ptr ty p |--
      valid_ptr (p ,, o_sub σ ty 1).
    Proof. iDestruct 1 as "(_ & _ & _ & _ & $)". Qed.

    Lemma type_ptr_erase : forall ty p,
        type_ptr ty p -|- type_ptr (erase_qualifiers ty) p.
    Proof.
      rewrite /type_ptr; intros.
      rewrite -aligned_ptr_ty_erase_qualifiers size_of_erase_qualifiers; iFrame "#%".
      iSplit.
      { iIntros "(%&%&%&#?&#?)"; iFrame "#%".
        admit. (* [o_sub] is independent of qualifiers *) }
      { iIntros "(%&%&%&#?&?)"; iFrame "#%".
        admit. }
    Admitted.

    Lemma type_ptr_aligned_pure ty p :
      type_ptr ty p |-- [| aligned_ptr_ty ty p |].
    Proof. iDestruct 1 as "(_ & $ & _)". Qed.

    Lemma type_ptr_size ty p : type_ptr ty p |-- [| is_Some (size_of σ ty) |].
    Proof. iDestruct 1 as "(_ & _ & % & _)"; eauto. Qed.


    (* This lemma is unused; it confirms we can lift the other half of
    [pinned_ptr_aligned_divide], but we don't expose this. *)
    #[local] Lemma pinned_ptr_type_divide_2 {va n p ty}
      (Hal : align_of ty = Some n) (Hnn : p <> nullptr) :
      pinned_ptr va p ⊢ valid_ptr (p ,, o_sub σ ty 1) -∗
      [| (n | va)%N |] -∗ type_ptr ty p.
    Proof.
      rewrite /type_ptr /aligned_ptr_ty Hal /=.
      iIntros "[V [%P|[%P P]]] #$ %HvaAl"; first by case P.
      iFrame (Hnn).
      (* iDestruct (pinned_ptr_valid with "P") as "#$". *)
      iSplit; last admit.
      iExists _; iSplit; first done.
      iIntros "!%". rewrite /aligned_ptr.
      naive_solver.
    Admitted.

    (* XXX move *)
    Axiom align_of_uchar : align_of Tuchar = Some 1%N.

    (* Requirememnt is too strong, we'd want just [(strict_)valid_ptr p]; see comment
    above on [aligned_ptr_mpred] and [mem_inj_own].
    XXX: this assumes that casting to uchar preserves the pointer.
    *)
    #[local] Lemma valid_type_uchar p (Hnn : p <> nullptr) va :
      pinned_ptr va p ⊢
      valid_ptr (p ,, o_sub σ Tuchar 1) -∗
      type_ptr Tuchar p.
    Proof.
      iIntros "#P #V".
      iApply (pinned_ptr_type_divide_2 (n := 1)) => //. {
        exact: align_of_uchar. }
      iIntros "!%". exact: N.divide_1_l.
    Qed.

    (* todo(gmm): this isn't accurate, but it is sufficient to show that the axioms are
    instantiatable. *)
    Definition mdc_path {_ : genv} (this : globname) (most_derived : list globname)
               (q : cQp.t) (p : ptr) : mpred :=
      strict_valid_ptr p ** derivation_own p q this most_derived.

    Instance mdc_path_cfractional this mdc : CFractional1 (mdc_path this mdc) := _.
    Axiom mdc_path_cfrac_valid : forall cls path,
      CFracValid1 (mdc_path cls path).
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
        oaddr_encodes t q oa p v.
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

    #[global] Instance tptsto_agree ty q1 q2 p v1 v2 :
      Observe2 [| v1 = v2 |] (tptsto ty q1 p v1) (tptsto ty q2 p v2).
    Proof.
      intros; apply: observe_2_intro_persistent.
      iDestruct 1 as (Hnn1 Ht1 oa1) "H1".
      iDestruct 1 as (Hnn2 Ht2 oa2) "H2".
      iDestruct (observe_2_elim_pure (oa1 = oa2) with "H1 H2") as %->.
      destruct oa2; [iApply (observe_2 with "H1 H2") |].
      iDestruct (observe_2 [| v1 = v2 |] with "H1 H2") as %->.
      by iPureIntro.
    Qed.

    Axiom same_address_eq_type_ptr : forall ty p1 p2 n,
      same_address p1 p2 ->
      size_of σ ty = Some n ->
      (* if [ty = Tuchar], one of these pointer could provide storage for the other. *)
      ty <> Tuchar ->
      (n > 0)%N ->
      type_ptr ty p1 ∧ type_ptr ty p2 ∧ live_ptr p1 ∧ live_ptr p2 ⊢
        |={↑pred_ns}=> [| p1 = p2 |].

    (* Not provable in the current model without tying to a concrete model of pointers. *)
    Lemma offset_pinned_ptr_pure o z va p :
      eval_offset σ o = Some z ->
      ptr_vaddr p = Some va ->
      valid_ptr (p ,, o) |--
      [| 0 <= Z.of_N va + z |]%Z **
      [| ptr_vaddr (p ,, o) = Some (Z.to_N (Z.of_N va + z)) |].
    Proof.
      intros E P.
    Abort.

    Axiom offset_pinned_ptr_pure : forall σ o z va p,
      eval_offset σ o = Some z ->
      pinned_ptr_pure va p ->
      valid_ptr (p ,, o) |--
      [| 0 <= Z.of_N va + z |]%Z **
      [| ptr_vaddr (p ,, o) = Some (Z.to_N (Z.of_N va + z)) |].

    Axiom offset_inv_pinned_ptr_pure : forall σ o z va p,
      eval_offset σ o = Some z ->
      pinned_ptr_pure va (p ,, o) ->
      valid_ptr (p ,, o) |--
      [| 0 <= Z.of_N va - z |]%Z **
      [| pinned_ptr_pure (Z.to_N (Z.of_N va - z)) p |].

  End with_cpp.

    Parameter exposed_aid : forall `{!cpp_logic thread_info Σ}, alloc_id -> mpred.

  Section with_cpp.
    Context `{!cpp_logic thread_info Σ} {σ}.
    (* strict validity (not past-the-end) *)
    Notation strict_valid_ptr := (_valid_ptr Strict).
    (* relaxed validity (past-the-end allowed) *)
    Notation valid_ptr := (_valid_ptr Relaxed).

    Axiom exposed_aid_persistent : forall aid, Persistent (exposed_aid aid).
    Axiom exposed_aid_affine : forall aid, Affine (exposed_aid aid).
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
    Proof. Admitted.

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
    Proof. Admitted.

    Definition strict_valid_if_not_empty_array (ty : type) : ptr -> mpred :=
      if zero_sized_array ty then valid_ptr else strict_valid_ptr.
    #[global] Instance stict_valid_if_not_empty_array_persistent ty p :
      Persistent (strict_valid_if_not_empty_array ty p).
    Proof. rewrite /strict_valid_if_not_empty_array. case_match; refine _. Qed.
    #[global] Instance stict_valid_if_not_empty_array_affine ty p :
      Affine (strict_valid_if_not_empty_array ty p).
    Proof. rewrite /strict_valid_if_not_empty_array. case_match; refine _. Qed.
    #[global] Instance stict_valid_if_not_empty_array_timeless ty p :
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

    Lemma stict_valid_if_not_empty_array_erase ty p :
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
        all: try apply stict_valid_if_not_empty_array_erase.
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

    #[local] Theorem tptsto_welltyped : forall p ty q (v : val),
      Observe (has_type_or_undef v ty) (tptsto ty q p v).
    Proof. Admitted.

    (* TODO: the [Notation] connects to the wrong definition *)
    #[local] Theorem tptsto_reference_to : forall p ty q (v : val),
      Observe (reference_to ty p) (tptsto ty q p v).
    Proof. Admitted.

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
      (* A proper proof requires redesigning valid_ptr *)
      rewrite /_valid_ptr; iDestruct 1 as "[%|H]"; first naive_solver.
      iDestruct "H" as (? base l h o zo) "(B & Rng & %Hoff & _)".
      destruct Hoff as (Heval & Habs).
    Admitted.

    (** Justified by [https://eel.is/c++draft/expr.add#4.1]. *)
    Axiom _valid_ptr_nullptr_sub_false : forall vt ty (i : Z) (_ : i <> 0),
      _valid_ptr vt (nullptr ,, o_sub σ ty i) |-- False.
    (*
    TODO Controversial; if [f] is the first field, [nullptr->f] or casts relying on
    https://eel.is/c++draft/basic.compound#4 might invalidate this.
    To make this valid, we could ensure our axiomatic semantics produces
    [nullptr] instead of [nullptr ., o_field]. *)
    (* Axiom _valid_ptr_nullptr_field_false : forall vt f,
      _valid_ptr vt (nullptr ,, o_field σ f) |-- False. *)

    (** These axioms are named after the predicate in the conclusion. *)

    (**
    TODO: The intended proof of [strict_valid_ptr_sub] assumes that, if [p']
    normalizes to [p ., [ ty ! i ]], then [valid_ptr p'] is defined to imply
    validity of all pointers from [p] to [p'].

    Note that `arrR` exposes stronger reasoning principles, but this might still be useful.
    *)
    Axiom strict_valid_ptr_sub : ∀ (i j k : Z) p ty vt1 vt2,
      (i <= j < k)%Z ->
      _valid_ptr vt1 (p ,, o_sub σ ty i) |--
      _valid_ptr vt2 (p ,, o_sub σ ty k) -* strict_valid_ptr (p ,, o_sub σ ty j).

    (** XXX: this axiom is convoluted but
    TODO: The intended proof of [strict_valid_ptr_field_sub] (and friends) is that
    (1) if [p'] normalizes to [p'' ., [ ty ! i ]], then [valid_ptr p'] implies
    [valid_ptr p''].
    (2) [p ,, o_field σ f ,, o_sub σ ty i] will normalize to [p ,, o_field
    σ f ,, o_sub σ ty i], without cancellation.
    *)
    Axiom strict_valid_ptr_field_sub : ∀ p ty (i : Z) f vt,
      (0 < i)%Z ->
      _valid_ptr vt (p ,, o_field σ f ,, o_sub σ ty i) |-- strict_valid_ptr (p ,, o_field σ f).

    (* TODO: can we deduce that [p] is strictly valid? *)
    Axiom _valid_ptr_field : ∀ p f vt,
      _valid_ptr vt (p ,, o_field σ f) |-- _valid_ptr vt p.
    (* TODO: Pointers to fields can't be past-the-end, right?
    Except 0-size arrays. *)
    (* Axiom strict_valid_ptr_field : ∀ p f,
      valid_ptr (p ,, o_field σ f) |--
      strict_valid_ptr (p ,, o_field σ f). *)
    (* TODO: if we add [strict_valid_ptr_field], we can derive
    [_valid_ptr_field] from just [strict_valid_ptr_field] *)
    (* Axiom strict_valid_ptr_field : ∀ p f,
      strict_valid_ptr (p ,, o_field σ f) |-- strict_valid_ptr p. *)

    (* TODO: maybe add a validity of offsets to allow stating this more generally. *)
    Axiom valid_o_sub_size : forall p ty i vt,
      _valid_ptr vt (p ,, o_sub σ ty i) |-- [| is_Some (size_of σ ty) |].

    Axiom type_ptr_o_base : forall derived base p,
      class_derives derived [base] ->
      type_ptr (Tnamed derived) p ⊢ type_ptr (Tnamed base) (p ,, _base derived base).

    Axiom type_ptr_o_field_type_ptr : forall p fld cls (st : Struct),
      glob_def σ cls = Some (Gstruct st) ->
      fld ∈ s_fields st →
      type_ptr (Tnamed cls) p ⊢ type_ptr fld.(mem_type) (p .,
        Field cls fld.(mem_name)).

    Axiom type_ptr_o_sub : forall p (m n : N) ty,
      (m < n)%N ->
      type_ptr (Tarray ty n) p ⊢ type_ptr ty (p ,, _sub ty m).

    Axiom type_ptr_o_sub_end : forall p (n : N) ty,
      type_ptr (Tarray ty n) p ⊢ valid_ptr (p ,, _sub ty n).

    Axiom o_base_directly_derives : forall p base derived,
      strict_valid_ptr (p ,, o_base σ derived base) |--
      [| directly_derives σ derived base |].

    Axiom o_derived_directly_derives : forall p base derived,
      strict_valid_ptr (p ,, o_derived σ base derived) |--
      [| directly_derives σ derived base |].
  End with_cpp.
End VALID_PTR.
