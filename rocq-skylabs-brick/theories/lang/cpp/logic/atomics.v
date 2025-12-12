(*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.iris.extra.proofmode.proofmode.
Require Import bluerock.iris.extra.bi.ChargeCompat.
Require Import bluerock.iris.extra.bi.atomic1.
Require Import bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.semantics.
Require Import bluerock.lang.cpp.logic.pred.
Require Import bluerock.lang.cpp.logic.path_pred.
Require Import bluerock.lang.cpp.logic.heap_pred.
Require Import bluerock.lang.cpp.logic.wp.
Require Import bluerock.lang.cpp.logic.call.

Export bluerock.iris.extra.bi.atomic1.

#[local] Open Scope Z_scope.

Section with_Σ.
  Context `{cpp_logic} {resolve : genv} (tu : translation_unit).
  Variables (M : coPset) (ρ : region).

  Implicit Type (Q : val → mpred). (* atomics do not throw *)

  #[local] Notation wp_operand := (wp_operand tu ρ).
  #[local] Notation wp_args := (wp_args tu ρ).

  (* Builtins for Atomic operations. We follow those provided by GCC.
   * https://gcc.gnu.org/onlinedocs/gcc/_005f_005fatomic-Builtins.html
   * LLVM also provides similar builtins.
   * http://llvm.org/docs/Atomics.html#libcalls-atomic
   *)
  (****** Wp Semantics for atomic operations
   * These are given in the style of function call axioms
   *)
  Parameter wp_atom :
      forall {resolve:genv}, coPset ->
        AtomicOp -> type (* the access type of the atomic operation *) ->
        list val -> (val -> mpred) -> mpred.

  Definition pointee_type (t : type) : option type :=
    match t with
    | Tptr t => Some t
    | _ => None
    end.

  Definition get_acc_type (ao : AtomicOp) (ret : type) (ts : list type) : option type :=
    match ts with
    | t :: _ => pointee_type (erase_qualifiers t)
    | _ => None
    end.

  (* note(hai)
    This allows opening general Iris invariants around atomic operations.
    This means resource trading can happen around atomic accesses.
    This does not hold for non-SC accesses: in general, non-SC accesses can only
    trade objective resources: those whose meaning does not depend on a thread's
    view. This is because non-SC accesses may not provide enough synchronization.

    Arbitrary resource trading holds for sequential consistency, but sequential
    consistency is only guaranteed if all accesses in a program are also SC.

    We conjecture that if arbitrary resource trading holds for SC-only locations
    even in the present of other non-SC locations. Intuitively, this is because,
    assuming that there is no location that has mixed SC and non-SC accesses,
    the total order S among accesses to SC locations must be consistent with the
    happens-before relation, so every access is synchronized with the next one
    in S and thus can observe any previous changes made to the invariant.

    In hardware, the synchonization is backed up by the fact that SC accesses
    are compiled such that there is at least a full barrier betwen an SC load
    and an SC store.
    See https://www.cl.cam.ac.uk/~pes20/cpp/cpp0xmappings.html *)
  Axiom wp_operand_atomic: forall ao es ty (Q : val → FreeTemps → epred),
       (let targs := List.map type_of es in
        match get_acc_type ao ty targs with
        | None => False
        | Some acc_type =>
          letI* vs, free := eval evaluation_order.nd (List.map wp_operand es) in
          wp_atom top ao acc_type vs (fun v => Q v free)
        end)
    |-- wp_operand (Eatomic ao es ty) Q.
  (** ^ TODO the calling convention for atomics should change to be
      more uniform. e.g. atomics should be treated more like builtin
      functions.
   *)

  #[local] Notation wp_atom' := (@wp_atom resolve M) (only parsing).

  (* Memory Ordering Patterns: Now we only have _SEQ_CST *)
  Definition _SEQ_CST := Vint 5.

  (* note: the following axioms have laters earlier than they should be.
   * it is ok, because these are provable given the timelessness of points
   * to, but in truth, these should be proven from more primitive axioms.
   *)

  (* note(gmm): these are used for reading and writing values shared between
   * threads.
   *)

  (* note(hai) Semantics of SEQ_CST (SC) accesses:
    - SC load has at least ACQUIRE load semantics.
    - SC store has at least RELEASE store semantics.
    - Additionally, there exists a total order S among all SC accesses
      (across all locations) and SC fences (REL_ACQ fences).
      S needs to respect strong happens-before [shb] but not happens-before
      [hb]. The two coincide when there is no mixing of SC and non-SC accesses
      to the same location.
      Not requiring S to respect hb allows for more optimizations on some
      architecture (see [RC11], and [C++draft,atomics#6])
      [shb] : https://eel.is/c++draft/intro.races#12
      [hb]  : https://eel.is/c++draft/intro.races#10
      [C++draft, atomics#6] : https://eel.is/c++draft/atomics#order-6
      [RC11] : https://plv.mpi-sws.org/scfix/

    Mixing SC and non-SC accesses is not recommended, because then the usually
    expected semantics of SC accesses are not guaranteed (see below). *)

  (** [wrap_shift] is used to allow mask-changing fupd for the physically atomic
    operations. Since our semantics is axiomatized, we don't have a intensional
    definition of physical atomicity. Instead, we can encode it logically as
    the ability to make mask-changing fupd, with a later in between to represent
    at most one step.

    Note that the notion of physical atomicity is defined informally, depending
    on the level of abstraction. For example, in hardware, these operations are
    atomic in the transanctional sense, where (something like) a lock can be
    used to mantain that no intermediate state is observable to anyone. At the
    language level, we can consider that physically atomic.

    Note also that the later is fixed in [wrap_shift], and we will use it in
    axioms with the form
      wrap_shift (fun Q, Pre ** (Post -* Q))
    which means that there is a later both before Pre and (Post -* Q). That is,
    when unfolding wrap_shift, we have axioms of the form:
      (∃ mid, |={M, mid}=> ▷ Pre ** ▷ (Post -* |={mid,M} Q)) |-- wp_atom ...
    Having the later before Pre is generally NOT always possible. However, in
    this module, our pre-conditions are always timeless (they are always
    points-tos) so this is OK. Furthermore, having a later in pre-conditions is
    also common in Iris, because while it doesn't make any difference
    soundness-wise, it is convenient for clients to be able strip some laters
    when providing the pre-conditions. *)
  Definition wrap_shift (F : (val -> mpred) -> mpred) (Q : val -> mpred) : mpred :=
    Exists mid, (|={M,mid}=> |> F (funI result => |={mid,M}=> Q result)).

  (* An SC load Ld reads a value that is written by:
    (1) the latest SEQ_CST store that is immediately before Ld in S, *or*
    (2) some non-SC store that is racing with (does not happen-before) any
      stores that is before Ld in S.
    To have the expected SC behavior (1), we need to exclude (2). A possible
    restriction is to simply require the location to be used with SC access only.
    In other words, the following rule only holds for SC-only locations. *)
  (* An SC load on the SC-only location p reads the latest value v of p.
    At the language level, this should be a physically atomic operation. *)
  Axiom wp_atom_load_cst :
    forall memorder (acc_type:type) (p : val) (Q : val -> mpred),
      [| memorder = _SEQ_CST |] **
      wrap_shift (fun Q =>
                    Exists v q,  _eqv p |-> primR acc_type q v ** (* pre *)
                                (_eqv p |-> primR acc_type q v -* Q v)) Q (* post *)
      |-- wp_atom' "__atomic_load_n" acc_type [p; memorder] Q.

  (* An SC store writes the latest value, unless there are racing (no hb)
    non-SC stores. The following rule only holds for SC-only locations. *)
  (* An SC store on the SC-only location p writes the latest value v of p.
    At the language level, this should be a physically atomic operation. *)
  (* TODO switch to has_type here. Maybe even in the axioms about ints. *)
  Axiom wp_atom_store_cst :
    forall memorder acc_type p Q v,
      [| memorder = _SEQ_CST |] **
      [| has_type_prop v acc_type |] **
      wrap_shift (fun Q => _eqv p |-> anyR acc_type 1$m ** (* pre *)
                          (_eqv p |-> primR acc_type 1$m v -* Q Vundef)) Q (* post *)
      |-- wp_atom' "__atomic_store_n" acc_type [p; memorder; v] Q.

  (* The following rule holds for SC-only locations, or *no-racing-store*
    locations.
    No-racing-store locations are those whose stores are properly synchronized
    among themselves and with RMWs. For example, RMW-only locations are
    no-racing-store locations. RELEASE-ACQUIRE RMWs on a RMW-only location
    always read and write the latest value. *)
  (* An SC atomic exchange sets the latest value to v and returns the previous
    latest value w.
    At the language level, this should be a physically atomic operation. *)
  Axiom wp_atom_exchange_n_cst :
    forall memorder acc_type p Q v,
      [| memorder = _SEQ_CST |] **
      [| has_type_prop v acc_type |] **
      wrap_shift (fun Q => Exists w,
                          _eqv p |-> primR acc_type 1$m w ** (* pre *)
                          (_eqv p |-> primR acc_type 1$m v -* Q w)) Q (* post *)
      |-- wp_atom' "__atomic_exchange_n" acc_type [p; memorder; v] Q.

  (* Again, all of the RMWs rules only read and write latest values if the
    location is SC-only or no-racing-store.
    This operation is not physically atomic, because more than one location are
    involved. See https://eel.is/c++draft/atomics.types.operations#23.
    However, it is logically atomic w.r.t. the atomic location `p`.
    The points-to of `p` can be provided logically atomically with the AU1, but
    the points-to's of `new_p` and `ret` are assumed to be provided locally. *)
  Axiom wp_atom_exchange_cst :
    forall memorder acc_type p Q new_p q ret new_v,
      [| memorder = _SEQ_CST |] **
      |> ((* local pre-cond *)
          (* new value new_v for p *)
          _eqv new_p |-> primR acc_type q new_v **
          (* placeholder for the original value of p *)
          _eqv ret |-> anyR acc_type 1$m) **
      AU1 <<∀ v, (* atomic pre-cond: latest value of p is v *)
              _eqv p |-> primR acc_type 1$m v >> @M,∅
              (* Masks: M is picked by the client, for the invariants that the
                client needs to provide the atomic pre/post. The empty mask ∅ is
                assumed by the prover of the rule, meaning that the prover doesn't
                need internal invariants. Since we are only axiomatizing the rule
                and not proving it, empty mask is OK. *)
          <<  (* atomic post-cond: latest value updated to new_v *)
              _eqv p |-> primR acc_type 1$m new_v,
            COMM ((* post-cond: the client can assume the local points-to, which
                    is returned by the rule, to prove its post condition Q *)
                  _eqv new_p |-> primR acc_type q new_v **
                  (* ret stores the previous latest value v *)
                  _eqv ret |-> primR acc_type 1$m v -* Q v) >>
      |-- wp_atom' "__atomic_exchange" acc_type [p; memorder; new_p; ret] Q.

  (* An SC compare and exchange n. This rule combines the postcondition for both
    success and failure case. In the failure case, we know that the values are
    different.
    This operation is not physically atomic, because more than one location are
    involved. However, it is logically atomic w.r.t. the atomic location `p`.
    The points-to of `p` can be provided logically atomically with the AU1, but
    the points-to of `expected_p` is assumed to be provided locally. *)
  (* TODO: this rule is currently only available to integers. It should be able
    to support pointers, but pointer comparison is more involved and will be
    handled in the future. Tracked by cpp2v-core#306. *)
  Axiom wp_atom_compare_exchange_n_cst :
    forall p expected_p expected_v desired weak succmemord failmemord Q sz sgn,
    let ty := Tnum sz sgn in
      [| weak = Vbool false |] **
      [| succmemord = _SEQ_CST |] ** [| failmemord = _SEQ_CST |] **
      (* local pre-cond : placeholder for the expected value *)
      |> _eqv expected_p |-> primR ty 1$m (Vint expected_v) **
      AU1 <<∀ v, (* atomic pre-cond: latest value of p is v *)
              _eqv p |-> primR ty 1$m (Vint v) >> @M,∅
          <<∃ (b : bool) (v' : Z), (* atomic post-cond: latest value is v' *)
              _eqv p |-> primR ty 1$m (Vint v') **
              (* - success case: p has value desired and expected_p unchanged, or
                 - failed case: p is unchanged, expected_p stores the value read
                  v, which is the latest one due to failmemord being SC. Also,
                  as a strong CMPXCHG we know that the values are different. *)
              [|    b = true  /\ v' = desired /\ v =  expected_v
                 \/ b = false /\ v' = v       /\ v <> expected_v |],
            COMM (* post-cond *)
                _eqv expected_p |-> primR ty 1$m (Vint v) -* Q (Vbool b) >>
      |-- wp_atom' "__atomic_compare_exchange_n" ty
                  [p; succmemord; expected_p; failmemord; Vint desired; weak] Q.

  Axiom wp_atom_compare_exchange_n_cst_bool :
    forall p expected_p expected_v desired weak succmemord failmemord Q,
    let ty := Tbool in
      [| weak = Vbool false |] **
      [| succmemord = _SEQ_CST |] ** [| failmemord = _SEQ_CST |] **
      (* local pre-cond : placeholder for the expected value *)
      |> _eqv expected_p |-> primR ty 1$m (Vbool expected_v) **
      AU1 <<∀ v, (* atomic pre-cond: latest value of p is v *)
              _eqv p |-> primR ty 1$m (Vbool v) >> @M,∅
          <<∃ (b : bool) (v' : bool), (* atomic post-cond: latest value is v' *)
              _eqv p |-> primR ty 1$m (Vbool v') **
              (* - success case: p has value desired and expected_p unchanged, or
                 - failed case: p is unchanged, expected_p stores the value read
                  v, which is the latest one due to failmemord being SC. Also,
                  as a strong CMPXCHG we know that the values are different. *)
              [|    b = true  /\ v' = desired /\ v =  expected_v
                 \/ b = false /\ v' = v       /\ v <> expected_v |],
            COMM (* post-cond *)
                _eqv expected_p |-> primR ty 1$m (Vbool v) -* Q (Vbool b) >>
      |-- wp_atom' "__atomic_compare_exchange_n" ty
                  [p; succmemord; expected_p; failmemord; Vbool desired; weak] Q.

  (* An SC weak compare exchange. This rule combines the postcondition for both
    success and failure case. Since a weak CMPXCHG can fail spuriously, we do
    not know that the values are different when it fails.
    This operation is not physically atomic, because more than one location are
    involved. However, it is logically atomic w.r.t. the atomic location `p`.
    The points-to of `p` can be provided logically atomically with the AU1, but
    the points-to of `expected_p` is assumed to be provided locally. *)
  (* TODO: support for pointers, see cpp2v-core#306. *)
  Axiom wp_atom_compare_exchange_n_cst_weak :
    forall p expected_p expected_v desired weak succmemord failmemord Q sz sgn,
      let ty := Tnum sz sgn in
      [| weak = Vbool true |] **
      [| succmemord = _SEQ_CST |] ** [| failmemord = _SEQ_CST |] **
      (* local pre-cond : placeholder for the expected value *)
      |> _eqv expected_p |-> primR ty 1$m (Vint expected_v) **
      AU1 <<∀ v, (* atomic pre-cond: latest value of p is v *)
              _eqv p |-> primR ty 1$m (Vint v) >> @M,∅
          <<∃ (b : bool) v', (* atomic post-cond: latest value is v' *)
              _eqv p |-> primR ty 1$m (Vint v') **
            (* - success case: p has value desired and expected_p unchanged, or
               - failed case: p is unchanged, expected_p stores the value read
                v. As a weak CMPXCHG we DO NOT know that the values are different. *)
              [|    b = true  /\ v' = desired /\ v =  expected_v
                 \/ b = false /\ v' = v |],
            COMM (* post-cond *)
                _eqv expected_p |-> primR ty 1$m (Vint v) -* Q (Vbool b) >>
      |-- wp_atom' "__atomic_compare_exchange_n" ty
                  [p; succmemord; expected_p; failmemord; Vint desired; weak] Q.

  (* TODO: unify with Tnum case *)
  Axiom wp_atom_compare_exchange_n_cst_weak_bool :
    forall p expected_p expected_v desired weak succmemord failmemord Q,
      let ty := Tbool in
      [| weak = Vbool true |] **
      [| succmemord = _SEQ_CST |] ** [| failmemord = _SEQ_CST |] **
      (* local pre-cond : placeholder for the expected value *)
      |> _eqv expected_p |-> primR ty 1$m (Vbool expected_v) **
      AU1 <<∀ v, (* atomic pre-cond: latest value of p is v *)
              _eqv p |-> primR ty 1$m (Vbool v) >> @M,∅
          <<∃ (b : bool) v', (* atomic post-cond: latest value is v' *)
              _eqv p |-> primR ty 1$m (Vbool v') **
            (* - success case: p has value desired and expected_p unchanged, or
               - failed case: p is unchanged, expected_p stores the value read
                v. As a weak CMPXCHG we DO NOT know that the values are different. *)
              [|    b = true  /\ v' = desired /\ v =  expected_v
                 \/ b = false /\ v' = v |],
            COMM (* post-cond *)
                _eqv expected_p |-> primR ty 1$m (Vbool v) -* Q (Vbool b) >>
      |-- wp_atom' "__atomic_compare_exchange_n" ty
                  [p; succmemord; expected_p; failmemord; Vbool desired; weak] Q.

  (* TODO: support for pointers, see cpp2v-core#306. *)
  Axiom wp_atom_compare_exchange_cst :
    forall q p expected_p desired_p weak succmemord failmemord Q
      sz sgn expected desired,
      let ty := Tnum sz sgn in
      [| weak = Vbool false |] **
      [| succmemord = _SEQ_CST |] ** [| failmemord = _SEQ_CST |] **
      |> ((* local pre-cond *)
          _eqv expected_p |-> primR ty 1$m (Vint expected) **
          _eqv desired_p |-> primR ty q (Vint desired)) **
      AU1 <<∀ v, (* atomic pre-cond: latest value of p is v *)
              _eqv p |-> primR ty 1$m (Vint v) >> @M,∅
          <<∃ (b : bool) v', (* atomic post-cond: latest value is v' *)
              _eqv p |-> primR ty 1$m (Vint v') **
            (* - success case: p has value desired and expected_p unchanged, or
               - failed case: p is unchanged, expected_p stores the value read v. *)
              [|    b = true  /\ v' = desired /\ v =  expected
                 \/ b = false /\ v' = v       /\ v <> expected |],
            COMM ((* post-cond *)
                  _eqv expected_p |-> primR ty 1$m (Vint v) **
                  _eqv desired_p |-> primR ty q (Vint desired) -* Q (Vbool b)) >>
      |-- wp_atom' "__atomic_compare_exchange" ty
                  [p; succmemord; expected_p; failmemord; desired_p; weak] Q.

  (* TODO: support for pointers, see cpp2v-core#306. *)
  Axiom wp_atom_compare_exchange_cst_weak :
    forall q p expected_p desired_p weak succmemord failmemord Q
      sz sgn expected desired,
      let ty := Tnum sz sgn in
      [| weak = Vbool true |] **
      [| succmemord = _SEQ_CST |] ** [| failmemord = _SEQ_CST |] **
      |> ((* local pre-cond *)
          _eqv expected_p |-> primR ty 1$m (Vint expected) **
          _eqv desired_p |-> primR ty q (Vint desired)) **
      AU1 <<∀ v, (* atomic pre-cond: latest value of p is v *)
              _eqv p |-> primR ty 1$m (Vint v) >> @M,∅
          <<∃ (b : bool) v', (* atomic post-cond: latest value is v' *)
              _eqv p |-> primR ty 1$m (Vint v') **
            (* - success case: p has value desired and expected_p unchanged, or
               - failed case: p is unchanged, expected_p stores the value read v. *)
              [|    b = true  /\ v' = desired /\ v = expected
                 \/ b = false /\ v' = v |],
            COMM ((* post-cond *)
                  _eqv expected_p |-> primR ty 1$m (Vint v) **
                  _eqv desired_p |-> primR ty q (Vint desired) -* Q (Vbool b)) >>
      |-- wp_atom' "__atomic_compare_exchange" ty
                  [p; succmemord; expected_p; failmemord; desired_p; weak] Q.

  (** Atomic operations use two's complement arithmetic. This
  definition presupposes that the [n_i] satisfy
  [n_i = n_i `mod` 2 ^ bitsZ sz], which the following axioms ensure
  via typing side-conditions. *)
  Definition atomic_eval (sz : int_rank) (sgn : signed)
      (op : Z -> Z -> Z) (n1 n2 : Z) : Z :=
    let r := op n1 n2 in
    if sgn is Signed then to_signed (int_rank.bitsize sz) r else to_unsigned (int_rank.bitsize sz) r.

  #[local] Notation at_eval sz sgn op n1 n2 :=
    (Unfold atomic_eval (atomic_eval sz sgn op n1 n2)) (only parsing).

  (* atomic fetch and xxx rule *)
  Definition wp_fetch_xxx_cst (ao : AtomicOp) (op : Z -> Z -> Z) : Prop :=
    forall p arg memorder Q sz sgn,
      let acc_type := Tnum sz sgn in
      [| memorder = _SEQ_CST |] **
      [| has_type_prop (Vint arg) acc_type |] **
      wrap_shift (fun Q =>
                    Exists n,
                    _eqv p |-> primR acc_type 1$m (Vint n) **
                    (let n' := at_eval sz sgn op n arg in
                      _eqv p |-> primR acc_type 1$m (Vint n') -* Q (Vint n))) Q
      |-- wp_atom' ao acc_type [p; memorder; Vint arg] Q.

  #[local] Notation fetch_xxx ao op :=
    (Unfold wp_fetch_xxx_cst (wp_fetch_xxx_cst ao op)) (only parsing).

  Let nand (a b : Z) : Z := Z.lnot (Z.land a b).

  Axiom wp_atom_fetch_add_cst  : fetch_xxx "__atomic_fetch_add"  Z.add.
  Axiom wp_atom_fetch_sub_cst  : fetch_xxx "__atomic_fetch_sub"  Z.sub.
  Axiom wp_atom_fetch_and_cst  : fetch_xxx "__atomic_fetch_and"  Z.land.
  Axiom wp_atom_fetch_xor_cst  : fetch_xxx "__atomic_fetch_xor"  Z.lxor.
  Axiom wp_atom_fetch_or_cst   : fetch_xxx "__atomic_fetch_or"   Z.lor.
  Axiom wp_atom_fetch_nand_cst : fetch_xxx "__atomic_fetch_nand" nand.

  (* atomic xxx and fetch rule *)
  Definition wp_xxx_fetch_cst (ao : AtomicOp) (op : Z -> Z -> Z) : Prop :=
    forall p arg memorder Q sz sgn,
      let acc_type := Tnum sz sgn in
      [| memorder = _SEQ_CST |] **
      [| has_type_prop (Vint arg) acc_type |] **
      wrap_shift (fun Q =>
                    Exists n,
                    _eqv p |-> primR acc_type 1$m (Vint n) **
                    (let n' := at_eval sz sgn op n arg in
                      _eqv p |-> primR acc_type 1$m (Vint n') -* Q (Vint n'))) Q
      |-- wp_atom' ao acc_type [p; memorder; Vint arg] Q.

  #[local] Notation xxx_fetch ao op :=
    (Unfold wp_xxx_fetch_cst (wp_xxx_fetch_cst ao op)) (only parsing).

  Axiom wp_atom_add_fetch_cst  : xxx_fetch "__atomic_add_fetch"  Z.add.
  Axiom wp_atom_sub_fetch_cst  : xxx_fetch "__atomic_sub_fetch"  Z.sub.
  Axiom wp_atom_and_fetch_cst  : xxx_fetch "__atomic_and_fetch"  Z.land.
  Axiom wp_atom_xor_fetch_cst  : xxx_fetch "__atomic_xor_fetch"  Z.lxor.
  Axiom wp_atom_or_fetch_cst   : xxx_fetch "__atomic_or_fetch"   Z.lor.
  Axiom wp_atom_nand_fetch_cst : xxx_fetch "__atomic_nand_fetch" nand.

  (** Derived AU1 specs *)

  Definition atom_load_cst_AU1 (ty : type) (p : val) (Q : val -> mpred) : mpred :=
    AU1 <<∀ v q, ▷ _eqv p |-> primR ty q v>> @M,∅
        <<       ▷ _eqv p |-> primR ty q v,
            COMM Q v >>.

  (* TODO : generalize with telescopes. *)
  Lemma AU1_atom_load_cst :
    forall memorder acc_type p Q,
      [| memorder = _SEQ_CST |] **
      atom_load_cst_AU1 acc_type p Q
      |-- wp_atom' "__atomic_load_n" acc_type [p; memorder] Q.
  Proof.
    intros. rewrite -wp_atom_load_cst.
    iIntros "[$ AU]".
    iExists ∅.
    iMod "AU" as (v q) "[Hp [_ Close]]".
    iIntros "!> !>". iExists v, q. iFrame "Hp".
    iIntros "Hp". iApply ("Close" with "Hp").
  Qed.

  Definition atom_store_cst_AU1 (ty : type) (p : val) (Q : val -> mpred) v : mpred :=
    AU1 << ▷ _eqv p |-> anyR ty 1$m >> @M,∅
        << ▷ _eqv p |-> primR ty 1$m v,
            COMM Q Vundef >>.

  Lemma AU1_atom_store_cst :
    forall memorder acc_type p Q v,
      [| memorder = _SEQ_CST |] **
      [| has_type_prop v acc_type |] **
      atom_store_cst_AU1 acc_type p Q v
      |-- wp_atom' "__atomic_store_n" acc_type [p; memorder; v] Q.
  Proof.
    intros. rewrite -wp_atom_store_cst.
    iIntros "[$ [$ AU]]".
    iExists ∅.
    iMod "AU" as "[$ Close]".
    iIntros "!> !> Hp". by iMod ("Close" with "Hp") as "$".
  Qed.

  Definition atom_exchange_n_cst_AU1 (ty : type) (p : val) (Q : val -> mpred) v : mpred :=
    AU1 <<∀ w, ▷ _eqv p |-> primR ty 1$m w >> @M,∅
        <<     ▷ _eqv p |-> primR ty 1$m v,
            COMM Q w >>.

  Lemma AU1_atom_exchange_n_cst :
    forall memorder acc_type p Q v,
      [| memorder = _SEQ_CST |] **
      [| has_type_prop v acc_type |] **
      atom_exchange_n_cst_AU1 acc_type p Q v
      |-- wp_atom' "__atomic_exchange_n" acc_type [p; memorder; v] Q.
  Proof.
    intros. rewrite -wp_atom_exchange_n_cst.
    iIntros "[$ [$ AU]]".
    iExists ∅.
    iMod "AU" as (w) "[Hp Close]".
    iIntros "!> !>". iExists w. iFrame "Hp".
    iIntros "Hp". by iMod ("Close" with "Hp") as "$".
  Qed.

  Definition atom_fetch_xxx_cst_AU1 (op : Z -> Z -> Z)
    ty (p : val) (z : Z) (Q : val -> mpred) sz sgn : mpred :=
    AU1 <<∀ n, ▷ _eqv p |-> primR ty 1$m (Vint n) >> @M,∅
        <<     let n' := at_eval sz sgn op n z in
              ▷ _eqv p |-> primR ty 1$m (Vint n'),
            COMM Q (Vint n) >>.

  Lemma AU1_atom_fetch_xxx_cst ao op :
    wp_fetch_xxx_cst ao op ->
    forall p arg memorder Q sz sgn,
      let acc_type := Tnum sz sgn in
      [| memorder = _SEQ_CST |] **
      [| has_type_prop (Vint arg) acc_type |] **
      atom_fetch_xxx_cst_AU1 op acc_type p arg Q sz sgn
      |-- wp_atom' ao acc_type [p; memorder; Vint arg] Q.
  Proof.
    intros WP. intros. rewrite -WP.
    iIntros "[$ [$ AU]]".
    iExists ∅.
    iMod "AU" as (w) "[Hp Close]".
    iIntros "!> !>". iExists w. iFrame "Hp".
    iIntros "Hp". by iMod ("Close" with "Hp") as "$".
  Qed.

  Definition AU1_atom_fetch_add_cst
    := AU1_atom_fetch_xxx_cst _ _ wp_atom_fetch_add_cst.
  Definition AU1_atom_fetch_sub_cst
    := AU1_atom_fetch_xxx_cst _ _ wp_atom_fetch_sub_cst.
  Definition AU1_atom_fetch_and_cst
    := AU1_atom_fetch_xxx_cst _ _ wp_atom_fetch_and_cst.
  Definition AU1_atom_fetch_xor_cst
    := AU1_atom_fetch_xxx_cst _ _ wp_atom_fetch_xor_cst.
  Definition AU1_atom_fetch_or_cst
    := AU1_atom_fetch_xxx_cst _ _ wp_atom_fetch_or_cst.
  Definition AU1_atom_fetch_nand_cst
    := AU1_atom_fetch_xxx_cst _ _ wp_atom_fetch_nand_cst.

  Definition atom_xxx_fetch_cst_AU1 (op : Z -> Z -> Z)
    ty (p : val) (z : Z) (Q : val -> mpred) sz sgn : mpred :=
    AU1 <<∀ n (n' := at_eval sz sgn op n z),
              ▷ _eqv p |-> primR ty 1$m (Vint n) >> @M,∅
        <<     ▷ _eqv p |-> primR ty 1$m (Vint n'),
            COMM Q (Vint n') >>.

  Lemma AU1_atom_xxx_fetch_cst ao op :
    wp_xxx_fetch_cst ao op ->
    forall p arg memorder Q sz sgn,
      let acc_type := Tnum sz sgn in
      [| memorder = _SEQ_CST |] **
      [| has_type_prop (Vint arg) acc_type |] **
      atom_xxx_fetch_cst_AU1 op acc_type p arg Q sz sgn
      |-- wp_atom' ao acc_type [p; memorder; Vint arg] Q.
  Proof.
    intros WP. intros. rewrite -WP.
    iIntros "[$ [$ AU]]".
    iExists ∅.
    iMod "AU" as (w) "[Hp Close]".
    iIntros "!> !>". iExists w. iFrame "Hp".
    iIntros "Hp". by iMod ("Close" with "Hp") as "$".
  Qed.

  Definition AU1_atom_add_fetch_cst
    := AU1_atom_xxx_fetch_cst _ _ wp_atom_add_fetch_cst.
  Definition AU1_atom_sub_fetch_cst
    := AU1_atom_xxx_fetch_cst _ _ wp_atom_sub_fetch_cst.
  Definition AU1_atom_and_fetch_cst
    := AU1_atom_xxx_fetch_cst _ _ wp_atom_and_fetch_cst.
  Definition AU1_atom_xor_fetch_cst
    := AU1_atom_xxx_fetch_cst _ _ wp_atom_xor_fetch_cst.
  Definition AU1_atom_or_fetch_cst
    := AU1_atom_xxx_fetch_cst _ _ wp_atom_or_fetch_cst.
  Definition AU1_atom_nand_fetch_cst
    := AU1_atom_xxx_fetch_cst _ _ wp_atom_nand_fetch_cst.
End with_Σ.
