(*
 * Copyright (c) 2020-2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(** This file defines the core logic (called [mpred]) that we use
    for C++.

    Known issues:
    - currently the logic is sequentially consistent
    - the memory model is simplified from the standard C++ memory
      model.
 *)
Require Import elpi.apps.locker.locker.
Require Export bluerock.prelude.addr.

Require Export bluerock.iris.extra.bi.prelude.
Require Export bluerock.iris.extra.bi.observe.
Require Export bluerock.iris.extra.bi.spec.knowledge.
Require Export bluerock.lang.cpp.reserved_notation.
Require Export bluerock.lang.cpp.logic.mpred.
Require Export bluerock.lang.cpp.logic.rep.
(** ^^ Delicate; export types and canonical structures (CS) for [monPred], [mpred] and [Rep].
Export order can affect CS inference. *)

Require Import bluerock.prelude.bytestring.

Require Export bluerock.lang.cpp.algebra.cfrac.
Require Export bluerock.lang.cpp.bi.cfractional.

Require Export iris.base_logic.lib.iprop.
(* TODO: ^^ only needed to export uPredI, should be removed. *)
Require Import iris.bi.lib.fractional.
Require Import bluerock.iris.extra.proofmode.proofmode.

Require Import bluerock.iris.extra.bi.na_invariants.
Require Import bluerock.iris.extra.bi.cancelable_invariants.
Export ChargeNotation.
Require Import bluerock.lang.cpp.bi.cfractional.

Require Import bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.semantics.values.
Require Import bluerock.lang.cpp.semantics.subtyping.

#[local] Set Printing Coercions.

Variant validity_type : Set := Strict | Relaxed.

Implicit Types (vt : validity_type) (σ : genv).
Implicit Types (n : N) (z : Z).

(* Namespace for the invariants of the C++ abstraction's ghost state. *)
Definition pred_ns : namespace := nroot .@@ "bluerock" .@@ "lang" .@@ "cpp_logic".

(* Used by [has_type_prop_has_type_noptr]. No theory. *)
Definition nonptr_prim_type (ty : type) : bool :=
  match drop_qualifiers ty with
  | Tfloat_ _ | Tchar_ _ | Tvoid | Tbool | Tenum _ | Tnum _ _ => true
  | Tnullptr | Tptr _ | Tref _ | Trv_ref _ | _ => false
  end.

Lemma nonptr_prim_type_erase_qualifiers : forall (ty : type),
    nonptr_prim_type ty = nonptr_prim_type (erase_qualifiers ty).
Proof. induction ty; simpl; eauto. Qed.

Module Type CPP_LOGIC
  (Import P : PTRS_INTF)
  (Import INTF : VALUES_INTF_FUNCTOR P)
  (Import CC : CPP_LOGIC_CLASS).

  Implicit Types (p : ptr).

  Section with_cpp.

    (**
      [_valid_ptr vt p] is a persistent assertion that [p] is a _valid pointer_, that is:
      - [p] can point to a function or a (possibly dead) object [o]
      - if [vt = Relaxed], [p] can be nullptr, or past-the-end of a (possibly dead) object [o].
      In particular, [_valid_ptr vt p] prevents producing [p] by incrementing
      past-the-end pointers into overflow territory.

      Our definition of validity includes all cases in which a pointer is not
      an _invalid pointer value_ in the sense of the standard
      (<https://eel.is/c++draft/basic.compound#3.1>), except that our concept
      of validity survives deallocation; a pointer is only valid according to
      the standard (or "standard-valid") if it is _both_ valid ([_valid_ptr
      vt p]) and live ([live_ptr p]); we require both where needed (e.g.
      [eval_ptr_eq]).

      When the duration of a region of storage ends [note 1], contained objects [o] go
      from live to dead, and pointers to such objects become _dangling_, or
      _invalid pointer values_ (<https://eel.is/c++draft/basic.compound#3.1>);
      this is called _pointer zapping_ [note 1].
      In our semantics, that only consumes the non-persistent predicate
      [live_ptr p], not the persistent predicate [_valid_ptr vt p].

      Following Cerberus, [live_alloc_id] tracks liveness per allocation
      ID (see comments for [ptr]), and [live_ptr] is derived from it. Hence,
      a pointer [p] past-the-end of [o] also becomes dangling when [o] is
      deallocated.

      It's implementation-defined whether invalid pointer values are
      (non-copyable) trap representations. Instead, we restrict to
      implementations where dangling pointers are not trap representations
      (which is allowed, since this choice is implementation-defined) and
      pointer zapping does not actually clear pointers.

      [Note 1]. See https://eel.is/c++draft/basic.stc.general#4 and
      https://eel.is/c++draft/basic.compound#3.1 for C++, and
      http://www.open-std.org/jtc1/sc22/wg14/www/docs/n2369.pdf for
      discussion in the context of the C standard.
    *)
    Parameter _valid_ptr : forall `{cpp_logic} (vt : validity_type) (p : ptr), mpred.
    (* strict validity (not past-the-end) *)
    Notation strict_valid_ptr := (_valid_ptr Strict).
    (* validity (past-the-end allowed) *)
    Notation valid_ptr := (_valid_ptr Relaxed).

  Section with_cpp_logic.
    Context `{cpp_logic} {σ}.

    #[global] Declare Instance _valid_ptr_persistent : forall b p, Persistent (_valid_ptr b p).
    #[global] Declare Instance _valid_ptr_affine : forall b p, Affine (_valid_ptr b p).
    #[global] Declare Instance _valid_ptr_timeless : forall b p, Timeless (_valid_ptr b p).

    Axiom valid_ptr_nullptr : |-- valid_ptr nullptr.
    Axiom not_strictly_valid_ptr_nullptr : strict_valid_ptr nullptr |-- False.
    Axiom strict_valid_valid : forall p,
      strict_valid_ptr p |-- valid_ptr p.

  End with_cpp_logic.

    (**
    [has_type v ty] is an approximation in [mpred] of "[v] is an initialized value
    of type [t]." This is intended to be preserved by the C++ type system.
    TODO: include in [primR].
    TODO: refine for which types https://bedrocksystems.atlassian.net/browse/FM-3760
    *)
    Parameter has_type : ∀ `{cpp_logic} {σ}, val -> type -> mpred.

    (**
       [reference_to ty p] states that the location [p] stores a value of type [ty].
       Being a reference is stronger than being a pointer because pointers allow
       past-the-end pointers while references do not.

       This should be thought of as closely related to [has_type (Vref p) (Tref ty)]
       except that it holds on types that are not valid C++ types. For example,
       if
       <<
       struct C { int& r; } x;
       >>
       then [reference_to (Tref Tint) (x ., ``::C::r``)].

       In the future, [has_type (Vref (x ., ``::C::r``)) (Tref (Tref Tint))]
       may not hold since [Tref (Tref Tint)] is not a valid C++ type. The
       current blocker to this is that we use [tptsto] to represent
       ownership of references. This would need to change.

       Note that the following code is (currently?) legal according to our
       semantics:
       <<
       { long x; *static_cast<int*>(&x); }
       >>
       because [reference_to] only guarantees alignment, not anything
       about the dynamic type of the object. Requiring a property of the dynamic
       type of the object would require us to carry type information in
       [strict_valid_ptr] (which would make it something like a pre-construction
       state of [type_ptr]).
     *)
    Parameter reference_to : forall `{cpp_logic} {σ}, type -> ptr -> mpred.

    Section with_genv.
      Context `{cpp_logic} {σ}.

      #[global] Declare Instance has_type_knowledge : Knowledge2 has_type.
      #[global] Declare Instance has_type_timeless : Timeless2 has_type.

      Axiom has_type_has_type_prop : ∀ v ty, has_type v ty |-- [| has_type_prop v ty |].

      Axiom has_type_prop_has_type_noptr : ∀ v ty,
        nonptr_prim_type ty ->
        [| has_type_prop v ty |] |-- has_type v ty.

      (* [has_type] is independent of qualifiers.
         This allows casting betweeen [const] and non-[const].
         *)
      Axiom has_type_erase_qualifiers : ∀ ty v,
        has_type v ty -|- has_type v (erase_qualifiers ty).

      (* Internal statements: *)
      Axiom has_type_nullptr' : ∀ p,
        has_type (Vptr p) Tnullptr -|- [| p = nullptr |].
      Axiom has_type_ptr' : ∀ p ty,
        has_type (Vptr p) (Tptr ty) -|-
        valid_ptr p ** [| aligned_ptr_ty ty p |].

      (* These two definitions are needed because of [tptsto_has_type] *)
      Axiom has_type_ref' : ∀ p ty,
        has_type (Vref p) (Tref ty) |-- reference_to ty p.
      Axiom has_type_rv_ref' : ∀ p ty,
        has_type (Vref p) (Trv_ref ty) |-- reference_to ty p.

      #[global] Declare Instance reference_to_knowledge : Knowledge2 reference_to.
      #[global] Declare Instance reference_to_timeless : Timeless2 reference_to.

      (* NOTE: this is almost derivable from [reference_to_intro] and
         [reference_to_elim] except for the issue with non-standard types. *)
      Axiom reference_to_erase : forall ty p,
          reference_to ty p -|- reference_to (erase_qualifiers ty) p.

      (** The introduction and elimination forms are not the same
          to avoid using [has_type] as types that are not C++ types.
          In practice, the only way to prove a [reference_to] is to have
          a [tptsto] assertion.

          **A note on 0-sized objects**
          0-sized objects are problematic from the point of view of C++ (they are not
          permitted by the standard, but they are supported by standard compilers).
          The problem with 0-sized objects is that they do not have a unique identity
          but the BRiCk semantics will give them an identity using
          [struct_padding]/[union_padding].

          Mitigation: We currently address this by forbidding reasoning about
                      constructors of 0-sized objects.
       *)
      Axiom reference_to_intro : forall ty p,
          strict_valid_ptr p |-- has_type (Vptr p) (Tptr ty) -* reference_to ty p.
      Axiom reference_to_elim : forall ty p,
          reference_to ty p |--
            [| aligned_ptr_ty ty p |] ** [| p <> nullptr |] **
            valid_ptr p ** if zero_sized_array ty then emp else strict_valid_ptr p.

    End with_genv.

    Parameter has_type_or_undef : forall `{cpp_logic} {σ}, val -> type -> mpred.
    Axiom has_type_or_undef_unfold : forall `{cpp_logic} {σ},
        @has_type_or_undef _ _ _ _ = funI v ty => has_type v ty \\// [| v = Vundef |].

    (** Formalizes the notion of "provides storage",
    http://eel.is/c++draft/intro.object#def:provides_storage *)
    Parameter provides_storage :
      forall `{cpp_logic} {σ} (storage : ptr) (object : ptr) (object_type : Rtype), mpred.

  Section with_cpp_logic.
    Context `{cpp_logic} {σ}.

    #[global] Declare Instance provides_storage_persistent :
      forall storage_ptr obj_ptr ty,
      Persistent (provides_storage storage_ptr obj_ptr ty).
    #[global] Declare Instance provides_storage_affine :
      forall storage_ptr obj_ptr ty,
      Affine (provides_storage storage_ptr obj_ptr ty).
    #[global] Declare Instance provides_storage_timeless :
      forall storage_ptr obj_ptr ty,
      Timeless (provides_storage storage_ptr obj_ptr ty).
  End with_cpp_logic.

    (** *** Typed points-to predicate.
    Fact [tptsto t q p v] asserts the following things:
    1. Pointer [p] points to value [v].
    2. We have fractional ownership [q] (in the separation logic sense).
    3. Pointer [p] points to a memory location with C++ type [t].
    However:
    1. Value [v] need not be initialized.
    2. Hence, [v] might not satisfy [has_type_prop t v].

    [tptsto] is only used to represent memory cells that contain
    values representable as a single [val]. This includes:
    - value types (see [is_value_type]), and
    - reference types. Note that all gl-values, i.e. x-values ([Trv_ref])
      and l-values ([Tref]), are represented using [Tref].
    These requirements justify the axiom [tptsto_valid_type].

    We use this predicate both for pointers to actual memory and for pointers to
    C++ locations that are not stored in memory (as an optimization).
    *)
    Parameter tptsto : forall `{cpp_logic} {σ}
      (t : Rtype) (q : cQp.t) (a : ptr) (v : val), mpred.

  Section with_cpp_logic.
    Context `{cpp_logic} {σ}.

    #[global] Declare Instance tptsto_valid_type
      : forall (t : Rtype) (q : cQp.t) (a : ptr) (v : val),
        Observe [| is_heap_type t |] (tptsto t q a v).

    Axiom tptsto_nonnull : forall {σ} ty q a,
      tptsto ty q nullptr a |-- False.

    #[global] Declare Instance tptsto_timeless : Timeless4 tptsto.
    #[global] Declare Instance tptsto_cfractional {σ} ty : CFractional2 (tptsto ty).

    #[global] Declare Instance tptsto_cfrac_valid {σ} t : CFracValid2 (tptsto t).

    #[global] Declare Instance tptsto_welltyped : forall {σ} p ty q v,
      Observe (has_type_or_undef v ty) (tptsto ty q p v).

    #[global] Declare Instance tptsto_reference_to : forall {σ} p ty q v,
      Observe (reference_to ty p) (tptsto ty q p v).

    (**
    NOTE: We'll eventually need the stronger [tptsto_learn : ∀ {σ} ty
    q1 q2 p v1 v2, <absorb> (tptsto ty q1 p v1) //\\ <absorb> (tptsto
    ty q2 p v2) |-- [! v1 = v2 !]] but setting up the proof in
    [simple_pred] now would be a bit of a digression.
    *)
    #[global] Declare Instance tptsto_agree : forall {σ} ty q1 q2 p v1 v2,
      Observe2 [| v1 = v2 |]
               (tptsto ty q1 p v1)
               (tptsto ty q2 p v2).

    End with_cpp_logic.

    (** The allocation is alive. Neither persistent nor fractional.
      See https://eel.is/c++draft/basic.stc.general#4 and
      https://eel.is/c++draft/basic.compound#3.1.
    *)
    Parameter live_alloc_id : forall `{cpp_logic},
      alloc_id -> mpred.

  Section with_cpp_logic.
    Context `{cpp_logic} {σ}.

    #[global] Declare Instance live_alloc_id_timeless : forall aid, Timeless (live_alloc_id aid).

    Axiom valid_ptr_alloc_id : forall p,
      valid_ptr p |-- [| is_Some (ptr_alloc_id p) |].

    (** This pointer is from a live allocation; this does not imply
    [_valid_ptr], because even overflowing offsets preserve the allocation ID.
    *)
    Definition live_ptr (p : ptr) :=
      default False%I (live_alloc_id <$> ptr_alloc_id p).

    (** We consider [nullptr] as live, following Krebbers, as a way to
    simplify stating rules for pointer comparison. *)
    Axiom nullptr_live : |-- live_ptr nullptr.

    Axiom tptsto_live : forall {σ} ty (q : cQp.t) p v,
      tptsto ty q p v |-- live_ptr p ** True.

  End with_cpp_logic.

    (** [mdc_path σ this mdc q p] state that [p] is a pointer to a (live)
        object of type [this] that is part of an object that can be reached
        using the *path* [mdc]. The ownership [mdc_path] is only exposed to
        the program for an object of class <<C>> if <<C>> has <<virtual>>
        methods (or base classes, which are not currently supported).
        - if [mdc = []] then this object mdc_path is not initialized yet,
          e.g. because its base classes are still being constructed.
        - otherwise, [mdc] is the *path* from the most derived class to this
          object. For example, suppose you have:
          <<
          struct A { virtual int f() { return 0; } };
          struct B : public A { virtual int f() { return 1; } };
          struct C : public A { };
          struct D : public B, public C { };

          int doA(A* a) { return a->f(); }
          int test() {
              D d;
              return doA(static_cast<B*>(&d)) /* = 1 */
                   + doA(static_cast<C*>(&d)) /* = 0 */;
          }
          >>
          for a fully constructed object of type `D` (at pointer [d]), you would
          have:
          [[
          mdc_path "::B" ["::D","::B"]      1 (d ., _base "::B") **
          mdc_path "::A" ["::D","::B","::A"] 1 (d ,, _base "::B" ,, _base "::A") **
          mdc_path "::A" ["::D","::C","::A"] 1 (d ,, _base "::C" ,, _base "::A")
          ]]
          in the partially constructed state, where "::D" has not yet been constructed
          but the base classes have been, you have the following:
          [[
          mdc_path "::B" ["::B"]      1 (d ., _base "::B") **
          mdc_path "::A" ["::B","::A"] 1 (d ,, _base "::B" ,, _base "::A") **
          mdc_path "::A" ["::C","::A"] 1 (d ,, _base "::C" ,, _base "::A")
          ]]
          Note that you do not get [mdc_path "::D" [] 1 d] at this point, you
          get [mdc_path "::D" ["::D"] 1 d] when you update all the other paths
          (but not atomically).

        [mdc_path] is primarily used to dispatch <<virtual>> function calls.
        Compilers can use the ownership here to represent dynamic dispatch
        tables.
     *)
    Parameter mdc_path : forall `{cpp_logic} {σ}
        (this : globname) (most_derived : list globname),
        cQp.t -> ptr -> mpred.

  Section with_cpp_logic.
    Context `{cpp_logic} {σ}.

    #[global] Declare Instance mdc_path_cfractional this mdc : CFractional1 (mdc_path this mdc).
    #[global] Declare Instance mdc_path_cfrac_valid cls path : CFracValid1 (mdc_path cls path).
    #[global] Declare Instance mdc_path_timeless : Timeless4 (mdc_path).
    #[global] Declare Instance mdc_path_strict_valid this mdc q p : Observe (strict_valid_ptr p) (mdc_path this mdc q p).
    #[global] Declare Instance mdc_path_agree cls1 cls2 q1 q2 p mdc1 mdc2 :
      Observe2 [| mdc1 = mdc2 /\ cls1 = cls2 |] (mdc_path cls1 mdc1 q1 p) (mdc_path cls2 mdc2 q2 p).

    (** this allows you to forget an object mdc_path, necessary for doing
        placement [new] over an existing object.
     *)
    Axiom mdc_path_forget : forall σ mdc this p,
        mdc_path this mdc 1$m p |-- |={↑pred_ns}=> mdc_path this nil 1$m p.

  End with_cpp_logic.

    (** the pointer points to the code

      note that in the presence of code-loading, function calls will
      require an extra side-condition that the code is loaded.
     *)
    Parameter code_at : forall `{cpp_logic} {σ},
      translation_unit -> Func -> ptr -> mpred.
    Parameter method_at : forall `{cpp_logic} {σ},
      translation_unit -> Method -> ptr -> mpred.
    Parameter ctor_at : forall `{cpp_logic} {σ},
      translation_unit -> Ctor -> ptr -> mpred.
    Parameter dtor_at : forall `{cpp_logic} {σ},
      translation_unit -> Dtor -> ptr -> mpred.


    Section with_genv.
      Context `{cpp_logic} {σ} (tu : translation_unit).

      #[local] Notation code_at := (code_at tu) (only parsing).
      #[local] Notation method_at := (method_at tu) (only parsing).
      #[local] Notation ctor_at := (ctor_at tu) (only parsing).
      #[local] Notation dtor_at := (dtor_at tu) (only parsing).

      #[global] Declare Instance code_at_persistent : forall f p, Persistent (code_at f p).
      #[global] Declare Instance code_at_affine : forall f p, Affine (code_at f p).
      #[global] Declare Instance code_at_timeless : forall f p, Timeless (code_at f p).

      #[global] Declare Instance method_at_persistent : forall f p, Persistent (method_at f p).
      #[global] Declare Instance method_at_affine : forall f p, Affine (method_at f p).
      #[global] Declare Instance method_at_timeless : forall f p, Timeless (method_at f p).

      #[global] Declare Instance ctor_at_persistent : forall f p, Persistent (ctor_at f p).
      #[global] Declare Instance ctor_at_affine : forall f p, Affine (ctor_at f p).
      #[global] Declare Instance ctor_at_timeless : forall f p, Timeless (ctor_at f p).

      #[global] Declare Instance dtor_at_persistent : forall f p, Persistent (dtor_at f p).
      #[global] Declare Instance dtor_at_affine : forall f p, Affine (dtor_at f p).
      #[global] Declare Instance dtor_at_timeless : forall f p, Timeless (dtor_at f p).

      Axiom code_at_live   : forall f p,   code_at f p |-- live_ptr p.
      Axiom method_at_live : forall f p, method_at f p |-- live_ptr p.
      Axiom ctor_at_live   : forall f p,   ctor_at f p |-- live_ptr p.
      Axiom dtor_at_live   : forall f p,   dtor_at f p |-- live_ptr p.

      Axiom code_at_strict_valid   : forall f p,   code_at f p |-- strict_valid_ptr p.
      Axiom method_at_strict_valid : forall f p, method_at f p |-- strict_valid_ptr p.
      Axiom ctor_at_strict_valid   : forall f p,   ctor_at f p |-- strict_valid_ptr p.
      Axiom dtor_at_strict_valid   : forall f p,   dtor_at f p |-- strict_valid_ptr p.

    End with_genv.

  Section with_cpp_logic.
    Context `{cpp_logic} {σ}.

    Axiom offset_pinned_ptr_pure : forall {o z va p},
      eval_offset σ o = Some z ->
      ptr_vaddr p = Some va ->
      valid_ptr (p ,, o) |--
      [| 0 <= Z.of_N va + z |]%Z **
      [| ptr_vaddr (p ,, o) = Some (Z.to_N (Z.of_N va + z)) |].

    Axiom offset_inv_pinned_ptr_pure : forall o z va p,
      eval_offset σ o = Some z ->
      ptr_vaddr (p ,, o) = Some va ->
      valid_ptr (p ,, o) |--
      [| 0 <= Z.of_N va - z |]%Z **
      [| ptr_vaddr p = Some (Z.to_N (Z.of_N va - z)) |].

    #[global] Declare Instance provides_storage_same_address : forall storage_ptr obj_ptr ty,
      Observe [| same_address storage_ptr obj_ptr |] (provides_storage storage_ptr obj_ptr ty).

    #[global] Declare Instance provides_storage_valid_storage_ptr : forall storage_ptr obj_ptr aty,
      Observe (valid_ptr storage_ptr) (provides_storage storage_ptr obj_ptr aty).
    #[global] Declare Instance provides_storage_valid_obj_ptr : forall storage_ptr obj_ptr aty,
      Observe (valid_ptr obj_ptr) (provides_storage storage_ptr obj_ptr aty).

  End with_cpp_logic.

    (**
    [exposed_aid aid] states that the storage instance identified by [aid] is
    "exposed" [1]. This enables int2ptr casts to produce pointers into this
    storage instance.

    [1] We use "exposed" in the sense defined by the N2577 draft C standard
    (http://www.open-std.org/jtc1/sc22/wg14/www/docs/n2577.pdf).
    See https://dl.acm.org/doi/10.1145/3290380 for an introduction.
    *)
    Parameter exposed_aid : forall `{cpp_logic}, alloc_id -> mpred.

  Section with_cpp_logic.
    Context `{cpp_logic} {σ}.

    #[global] Declare Instance exposed_aid_persistent : forall aid, Persistent (exposed_aid aid).
    #[global] Declare Instance exposed_aid_affine : forall aid, Affine (exposed_aid aid).
    #[global] Declare Instance exposed_aid_timeless : forall aid, Timeless (exposed_aid aid).

    Axiom exposed_aid_null_alloc_id : |-- exposed_aid null_alloc_id.

  End with_cpp_logic.

    (**
      [type_ptr (σ := σ) ty p] asserts that [p] points to
      a (possibly dead) object of type [ty] (in environment
      [σ]), as defined by https://eel.is/c++draft/basic.compound#3.1.

      This implies:
      - the pointer is strictly valid [type_ptr_strict_valid], and
        "p + 1" is also valid (while possibly past-the-end) [type_ptr_valid_plus_one].
      - the pointer is not (an offset of) null pointers [type_ptr_off_nonnull, type_ptr_nonnull]
      - the pointer is properly aligned [type_ptr_aligned_pure]

      [type_ptr] is persistent and survives deallocation of the pointed-to
      object, like [_valid_ptr].

      TODO: before a complete object is fully initialized,
      what [type_ptr] facts are available? For now, we only use [type_ptr]
      for fully initialized objects.
      Consider http://eel.is/c++draft/basic.memobj#basic.life, especially
      from http://eel.is/c++draft/basic.memobj#basic.life-1 to
      http://eel.is/c++draft/basic.memobj#basic.life-4.
     *)
    Parameter type_ptr : forall `{cpp_logic} {σ} (c : Rtype), ptr -> mpred.

  Section with_cpp_logic.
    Context `{cpp_logic} {σ}.

    #[global] Declare Instance type_ptr_persistent : forall p ty,
      Persistent (type_ptr ty p).
    #[global] Declare Instance type_ptr_affine : forall p ty,
      Affine (type_ptr ty p).
    #[global] Declare Instance type_ptr_timeless : forall p ty,
      Timeless (type_ptr ty p).

    Axiom type_ptr_erase : forall ty p,
        type_ptr ty p -|- type_ptr (erase_qualifiers ty) p.

    Axiom type_ptr_aligned_pure : forall ty p,
      type_ptr ty p |-- [| aligned_ptr_ty ty p |].

    Axiom type_ptr_off_nonnull : forall ty p o,
      type_ptr ty (p ,, o) |-- [| p <> nullptr |].

    #[global] Declare Instance tptsto_type_ptr : forall ty q p v,
      Observe (type_ptr ty p) (tptsto ty q p v).

    (* All objects in the C++ abstract machine have a size

       NOTE to support un-sized objects, we can simply say that the [sizeof] operator
            in C++ is only a conservative approximation of the true size of an object.
     *)
    Axiom type_ptr_size : forall ty p,
        type_ptr ty p |-- [| is_Some (size_of σ ty) |].

    (**
    Recall that [type_ptr] and [strict_valid_ptr] don't include
    past-the-end pointers... *)
    Axiom type_ptr_strict_valid : forall ty p,
      type_ptr ty p |-- strict_valid_ptr p.
    (** Hence they can be incremented into (possibly past-the-end) valid pointers. *)
    Axiom type_ptr_valid_plus_one : forall ty p,
      type_ptr ty p |-- valid_ptr (p ,, o_sub σ ty 1).

    (* When [p] is a [ptr] to a C++ object of type [ty], [p] is /also/ a pointer
       to the "object representation" of [ty] - which consists of "the sequence
       of [sizeof(ty)] unsigned char objects taken up by the object of
       type [ty]" [1].

       Detailed Justification:
       a) From the comment above the axiomatization of [type_ptr]:
          | [type_ptr ty p] asserts that [p] points to a (possibly dead) object of type [ty].
       b) In [basic.types.general#4] [1] the C++ Standard states that:
          | The object representation of an object of type T is the sequence of N unsigned
          | char objects taken up by the object of type T, where N equals sizeof(T).
       d) (NOTE: the C++ Standard lacks language regarding this point) the "object representation"
          for an object pointed to by [ptr] [p] is /also/ accessible via [p].
       e) (a)+(b)+(d) implies that a (potentially dead) object representation for type [ty]
          exists at [ptr] [p]
       f) (a)+(c)+(e) implies that [type_ptr Tbyte (p .[ Tbyte ! i ])] holds (regardless of whether
          not the object/"object representation" is alive)

       NOTE: There is no need to deal with past-the-end pointers explicitly since
       [type_ptr] explicitly excludes them; validity of past-the-end pointers
       can be established using [type_ptr_valid_plus_one].

       [1] <https://eel.is/c++draft/basic.types.general#4>
     *)
    Section type_ptr_object_representation.
      (* This section is intended to axiomatize a /sufficient/ and /sound/
         set of transport rules for [type_ptr] facts which can be used to
         satisfy the preconditions required when using [ptr_congP] to
         transport other resources.
       *)

      (* The following [Axiom] reflects a trivially faithful encoding of
         the quote from the C++ standard above [Section type_ptr_object_representation].

         NOTE: To practically use this [Axiom], [type_ptr] must be [Persistent];
         a reasonable alternative axiomatization which sidestepts this issue
         could produce /all/ of the [type_ptr] facts for the "object representation"
         at once:
         | ... ->
         |     type_ptr ty p
         | |-- [∗list] i ∈ seqN 0 (sizeof ty), type_ptr Tbyte (p .[ Tbyte ! i ])
       *)
      Section conservative.
        Axiom type_ptr_obj_repr_byte :
          forall (ty : Rtype) (p : ptr) (i sz : N),
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
            type_ptr ty p |-- type_ptr Tbyte (p ,, .[ Tbyte ! i ]).
      End conservative.

      (* NOTE: This might be reasonable to axiomatize directly; cf. the [NOTE] above
         [Section conservative].
       *)
      Section all_at_once.
        Lemma type_ptr_obj_repr :
          forall (ty : Rtype) (p : ptr) (sz : N),
            size_of σ ty = Some sz ->
            type_ptr ty p |-- [∗list] i ∈ seqN 0 sz, type_ptr Tbyte (p .[ Tbyte ! Z.of_N i ]).
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
      End all_at_once.
    End type_ptr_object_representation.

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
    Axiom tptsto_ptr_congP_transport : forall {σ} q p1 p2 v,
      ptr_congP σ p1 p2 |-- tptsto Tbyte q p1 v -* tptsto Tbyte q p2 v.

    (**
     ** Deducing pointer equalities
     The following axioms, together with [same_address_o_sub_eq], enable going
     from [same_address] (produced by C++ pointer equality) to actual pointer
     equalities.
     *)

    (** Pointer equality with [nullptr] is easy, as long as your pointer is valid.
     Validity is necessary: the C++ expression [(char * )p - (uintptr_t) p]
     produces an invalid pointer with address 0, which is not [nullptr] because
     it preserves the provenance of [p]. *)
    Axiom same_address_eq_null : forall p tv,
      _valid_ptr tv p |--
      [| same_address p nullptr <-> p = nullptr |].

    (**
    [same_address_eq_type_ptr] concludes that two pointers [p1] and [p2] are
    equal if they have the same address, point to live objects [o1] and [o2],
    and have the same (non-uchar) type [ty] with nonzero size.

    Justifying this from the standard is tricky; here's a proof sketch.
    - Because [ty] has "nonzero size" (https://eel.is/c++draft/intro.object#8),
      and we don't support bitfields, we apply the standard:

      > Unless it is a bit-field, an object with nonzero size shall occupy one
        or more bytes of storage, including every byte that is occupied in full
        or in part by any of its subobjects.

    - Because [o1] and [o2] are live, these objects share storage, hence they
      must coincide or one must be nested inside the other
      (https://eel.is/c++draft/intro.object#4); if they coincide, our proof
      is done.
    - Because [ty] is not [unsigned char], neither pointer can provide storage
      for the other (https://eel.is/c++draft/intro.object#3); so one must be a
      subobject of the other.
    - Since [o1] and [o2] have type [ty], and type [ty] has "nonzero size",
      neither of [o1] and [o2] can be a subobject of the other;
      we conjecture is provable from the C++ type system.

    NOTE: we check "nonzero size"
    (https://eel.is/c++draft/basic.memobj#intro.object-8) using [size_of],
    which might incorporate implementation-specific compiler decisions.
    TODO: handle [std::byte] like [unsigned char].
    *)
    Axiom same_address_eq_type_ptr : forall ty p1 p2 n,
      same_address p1 p2 ->
      size_of _ ty = Some n ->
      (* if [ty = Tuchar], one of these pointer could provide storage for the other. *)
      ty <> Tuchar ->
      (n > 0)%N ->
      type_ptr ty p1 ∧ type_ptr ty p2 ∧ live_ptr p1 ∧ live_ptr p2 ⊢
        |={↑pred_ns}=> [| p1 = p2 |].

  End with_cpp_logic.

    (** Padding
        [struct_padding] and [union_padding] represent the object state of an aggregate.
        Ownership of this token implies that the object is a alive. They only given when
        an object is fully constructed, and are taken back at the end of the lifetime.
        This is related to the "construction state" in Tahina's work, i.e.
        <https://inria.hal.science/file/index/docid/674663/filename/cpp-construction.pdf>
     *)
    Axiom struct_padding : forall `{cpp_logic} {σ},
      ptr -> globname -> cQp.t -> mpred.

  Section with_cpp_logic.
    Context `{cpp_logic} {σ}.

    #[global] Declare Instance struct_padding_timeless : Timeless3 struct_padding.
    #[global] Declare Instance struct_padding_fractional : forall p cls, CFractional (struct_padding p cls).
    #[global] Declare Instance struct_padding_frac_valid : forall p cls, CFracValid0 (struct_padding p cls).

    #[global] Declare Instance struct_padding_type_ptr_observe : forall p cls q,
        Observe (type_ptr (Tnamed cls) p) (struct_padding p cls q).

  End with_cpp_logic.

  (** [union_padding cls q active_member] is [q] ownership of
    the union padding for union [cls] for the active member
    [active_member]. When there is no active member the [active_member]
    is [None], otherwise it is [Some idx] where [idx] is the numeric
    index of member field.
    *)
  Parameter union_padding : forall `{cpp_logic} {σ},
    ptr -> globname -> cQp.t -> option nat -> mpred.

  Section with_cpp_logic.
    Context `{cpp_logic} {σ}.

    #[global] Declare Instance union_padding_timeless :  Timeless4 union_padding.
    #[global] Declare Instance union_padding_fractional : forall p cls, CFractional1 (union_padding p cls).
    #[global] Declare Instance union_padding_frac_valid : forall p cls, CFracValid1 (union_padding p cls).

    #[global] Declare Instance union_padding_type_ptr_observe : forall p cls q active,
        Observe (type_ptr (Tnamed cls) p) (union_padding p cls q active).
    #[global] Declare Instance union_padding_agree : forall p cls q q' i i',
        Observe2 [| i = i' |] (union_padding p cls q i) (union_padding p cls q' i').

  End with_cpp_logic.

  End with_cpp.

  (* strict validity (not past-the-end) *)
  Notation strict_valid_ptr := (_valid_ptr Strict).
  (* validity (past-the-end allowed) *)
  Notation valid_ptr := (_valid_ptr Relaxed).
End CPP_LOGIC.

(* Pointer axioms. XXX Not modeled for now. *)
Module Type VALID_PTR_AXIOMS
  (Import P : PTRS_INTF)
  (Import INTF : VALUES_INTF_FUNCTOR P)
  (Import CC : CPP_LOGIC_CLASS)
  (Import CPP : CPP_LOGIC P INTF CC).

  Implicit Types (p : ptr).

  Section with_cpp.
    Context `{cpp_logic} {σ}.

    Axiom invalid_ptr_invalid : forall vt,
      _valid_ptr vt invalid_ptr |-- False.

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
    Axiom strict_valid_ptr_field_sub : ∀ (p : ptr) ty (i : Z) f vt,
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

    (* We're ignoring virtual inheritance here, since we have no plans to
    support it for now, but this might hold there too. *)
    Axiom o_base_directly_derives : forall p base derived,
      strict_valid_ptr (p ,, o_base σ derived base) |--
      [| directly_derives σ derived base |].

    Axiom o_derived_directly_derives : forall p base derived,
      strict_valid_ptr (p ,, o_derived σ base derived) |--
      [| directly_derives σ derived base |].

    (* TODO: maybe add a validity of offsets to allow stating this more generally. *)
    Axiom valid_o_sub_size : forall p ty i vt,
      _valid_ptr vt (p ,, o_sub σ ty i) |-- [| is_Some (size_of σ ty) |].

    Axiom type_ptr_o_base : forall derived base p,
      class_derives derived [base] ->
      type_ptr (Tnamed derived) p ⊢ type_ptr (Tnamed base) (p ,, _base derived base).

    (*
    Axiom type_ptr_o_field_type_ptr : forall p fld cls st,
      glob_def σ cls = Some (Gstruct st) ->
      fld ∈ s_fields st →
         type_ptr (Tnamed cls) p
      ⊢ type_ptr fld.(mem_type) (p ., Field cls fld.(mem_name)). (* TODO field names *)
      *)

    Axiom type_ptr_o_sub : forall p (m n : N) ty,
      (m < n)%N ->
      type_ptr (Tarray ty n) p ⊢ type_ptr ty (p ,, _sub ty m).
  End with_cpp.
End VALID_PTR_AXIOMS.

Declare Module L : CPP_LOGIC PTRS_INTF_AXIOM VALUES_INTF_AXIOM LC.
Export L.

Declare Module Export VALID_PTR : VALID_PTR_AXIOMS PTRS_INTF_AXIOM VALUES_INTF_AXIOM LC L.

Section valid_ptr_code.
  Context `{cpp_logic} {σ} (tu : translation_unit).

  Lemma code_at_valid   : forall f p,   code_at tu f p |-- valid_ptr p.
  Proof. intros. rewrite code_at_strict_valid; apply strict_valid_valid. Qed.
  Lemma method_at_valid : forall f p, method_at tu f p |-- valid_ptr p.
  Proof. intros. rewrite method_at_strict_valid; apply strict_valid_valid. Qed.
  Lemma ctor_at_valid   : forall f p,   ctor_at tu f p |-- valid_ptr p.
  Proof. intros. rewrite ctor_at_strict_valid; apply strict_valid_valid. Qed.
  Lemma dtor_at_valid   : forall f p,   dtor_at tu f p |-- valid_ptr p.
  Proof. intros. rewrite dtor_at_strict_valid; apply strict_valid_valid. Qed.
End valid_ptr_code.

mlock Definition exposed_ptr `{cpp_logic} p : mpred :=
  valid_ptr p ** ∃ aid, [| ptr_alloc_id p = Some aid |] ** exposed_aid aid.

(** Physical representation of pointers. *)
(** [pinned_ptr va p] states that the abstract pointer [p] is tied to a
  virtual address [va].
  [pinned_ptr] will only hold on pointers that are associated to addresses,
  but other pointers exist. *)
mlock Definition pinned_ptr `{cpp_logic} {σ} (va : vaddr) (p : ptr) : mpred :=
  [| ptr_vaddr p = Some va |] ** exposed_ptr p.

Notation pinned_ptr_Z va p :=
  ([| 0 <= va |]%Z ** pinned_ptr (Z.to_N va) p).

Section pinned_ptr_def.
  Context `{cpp_logic} {σ}.

  #[global] Instance exposed_ptr_persistent p : Persistent (exposed_ptr p).
  Proof. rewrite exposed_ptr.unlock. apply _. Qed.
  #[global] Instance exposed_ptr_affine p : Affine (exposed_ptr p).
  Proof. rewrite exposed_ptr.unlock. apply _. Qed.
  #[global] Instance exposed_ptr_timeless p : Timeless (exposed_ptr p).
  Proof. rewrite exposed_ptr.unlock. apply _. Qed.
  #[global] Instance exposed_ptr_valid p :
    Observe (valid_ptr p) (exposed_ptr p).
  Proof. rewrite exposed_ptr.unlock. apply _. Qed.

  Lemma exposed_ptr_nullptr : |-- exposed_ptr nullptr.
  Proof.
    rewrite exposed_ptr.unlock ptr_alloc_id_nullptr.
    iDestruct valid_ptr_nullptr as "$". iExists _.
    by iDestruct exposed_aid_null_alloc_id as "$".
  Qed.

  Lemma offset2_exposed_ptr p o1 o2 :
    valid_ptr (p ,, o2) |-- exposed_ptr (p ,, o1) -* exposed_ptr (p ,, o2).
  Proof.
    rewrite exposed_ptr.unlock.
    iIntros "#V2 #[V1 E]"; iFrame "V2".
    iDestruct (valid_ptr_alloc_id with "V1") as %?.
    iDestruct (valid_ptr_alloc_id with "V2") as %?.
    by rewrite ptr_alloc_id_offset // ptr_alloc_id_offset.
  Qed.

  Lemma offset_exposed_ptr p o :
    valid_ptr (p ,, o) |-- exposed_ptr p -* exposed_ptr (p ,, o).
  Proof. rewrite -{2}(offset_ptr_id p). apply offset2_exposed_ptr. Qed.

  Lemma offset_inv_exposed_ptr p o :
    valid_ptr p |-- exposed_ptr (p ,, o) -* exposed_ptr p.
  Proof. rewrite -{1 3}(offset_ptr_id p). apply offset2_exposed_ptr. Qed.

  Lemma offset_exposed_ptr_all p o :
    valid_ptr p ∗ valid_ptr (p ,, o) ⊢ exposed_ptr p ∗-∗ exposed_ptr (p ,, o).
  Proof.
    iIntros "#[V V']"; iSplit.
    by iApply offset_exposed_ptr.
    by iApply offset_inv_exposed_ptr.
  Qed.

  #[global] Instance pinned_ptr_persistent va p : Persistent (pinned_ptr va p).
  Proof. rewrite pinned_ptr.unlock. apply _. Qed.
  #[global] Instance pinned_ptr_affine va p : Affine (pinned_ptr va p).
  Proof. rewrite pinned_ptr.unlock. apply _. Qed.
  #[global] Instance pinned_ptr_timeless va p : Timeless (pinned_ptr va p).
  Proof. rewrite pinned_ptr.unlock. apply _. Qed.

  Lemma pinned_ptr_intro p va :
    ptr_vaddr p = Some va -> exposed_ptr p |-- pinned_ptr va p.
  Proof. rewrite pinned_ptr.unlock. by iIntros (?) "$". Qed.

  #[global] Instance pinned_ptr_ptr_vaddr va p :
    Observe [| ptr_vaddr p = Some va |] (pinned_ptr va p).
  Proof. rewrite pinned_ptr.unlock. apply _. Qed.

  Lemma pinned_ptr_change_va_eq (p : ptr) (va va' : vaddr)
    (Heq : ptr_vaddr p = Some va) :
    pinned_ptr va' p |--  [| va' = va |] ** pinned_ptr va p.
  Proof.
    iIntros "#P".
    iDestruct (observe_elim_pure (ptr_vaddr p = Some va') with "P") as %?.
    simplify_eq. auto.
  Qed.

  Lemma pinned_ptr_change_va p va va'
    (Heq : ptr_vaddr p = Some va) :
    pinned_ptr va' p |-- pinned_ptr va p.
  Proof. rewrite pinned_ptr_change_va_eq //. by iIntros "[_ $]". Qed.

  #[global] Instance pinned_ptr_agree va1 va2 p :
    Observe2 [| va1 = va2 |] (pinned_ptr va1 p) (pinned_ptr va2 p).
  Proof.
    iIntros "#P1 #P2 !>".
    iDestruct (observe_elim_pure (_ = _) with "P1") as %?.
    iDestruct (observe_elim_pure (_ = _) with "P2") as %?; simplify_eq.
    by [].
  Qed.

  #[global] Instance pinned_ptr_valid va p :
    Observe (valid_ptr p) (pinned_ptr va p).
  Proof. rewrite pinned_ptr.unlock. apply _. Qed.

  (** Just a corollary of [provides_storage_same_address] in the style of
  [provides_storage_pinned_ptr]. *)
  Lemma provides_storage_pinned_ptr_pure {storage_ptr obj_ptr aty va} :
    ptr_vaddr storage_ptr = Some va ->
    provides_storage storage_ptr obj_ptr aty |-- [| ptr_vaddr obj_ptr = Some va |].
  Proof. rewrite provides_storage_same_address. by iIntros (HP <-). Qed.
End pinned_ptr_def.

Section with_cpp.
  Context `{cpp_logic} {σ}.

  Lemma same_address_bool_null p tv :
    _valid_ptr tv p |--
    [| same_address_bool p nullptr = bool_decide (p = nullptr) |].
  Proof. rewrite same_address_eq_null; iIntros "!%". apply bool_decide_ext. Qed.

  Lemma valid_ptr_zero_null p :
    ptr_vaddr p = Some 0%N ->
    valid_ptr p |-- [| p = nullptr |].
  Proof.
    rewrite same_address_eq_null.
    iIntros (Haddr [Hsuff _]) "!%". apply: Hsuff.
    rewrite same_address_iff ptr_vaddr_nullptr; naive_solver.
  Qed.

  Lemma valid_ptr_nonnull_nonzero p :
    p <> nullptr ->
    valid_ptr p |-- [| ptr_vaddr p <> Some 0%N |].
  Proof.
    destruct (decide (ptr_vaddr p = Some 0%N)); last naive_solver.
    rewrite valid_ptr_zero_null; naive_solver.
  Qed.

  Lemma type_ptr_nonnull ty p :
    type_ptr ty p |-- [| p <> nullptr |].
  Proof. rewrite -{1}(offset_ptr_id p). apply type_ptr_off_nonnull. Qed.

  #[global] Instance type_ptr_observe_nonnull ty p :
    Observe [| p <> nullptr |] (type_ptr ty p).
  Proof. rewrite type_ptr_nonnull. refine _. Qed.

  #[global] Instance provides_storage_preserves_nullptr {storage_ptr obj_ptr aty} :
    Observe [| storage_ptr = nullptr <-> obj_ptr = nullptr |] (provides_storage storage_ptr obj_ptr aty).
  Proof.
    apply observe_intro_only_provable; iIntros "PS".
    iDestruct (provides_storage_same_address with "PS") as %Hsm.
    iDestruct (provides_storage_valid_obj_ptr with "PS") as "#VO".
    iDestruct (provides_storage_valid_storage_ptr with "PS") as "#VS {PS}".
    iDestruct (same_address_eq_null with "VO") as %[HeqO _].
    iDestruct (same_address_eq_null with "VS") as %[HeqS _].
    iIntros "!%"; split; intros ->.
    - apply HeqO, symmetry, Hsm.
    - apply HeqS, Hsm.
  Qed.

  #[global] Instance provides_storage_preserves_nonnull {storage_ptr obj_ptr aty} :
    Observe [| storage_ptr <> nullptr <-> obj_ptr <> nullptr |] (provides_storage storage_ptr obj_ptr aty).
  Proof.
    apply observe_intro_only_provable. iIntros "PS".
    by iDestruct (provides_storage_preserves_nullptr with "PS") as "#-> {PS}".
  Qed.

  #[global] Instance pinned_ptr_unique va va' p :
    Observe2 [| va = va' |] (pinned_ptr va p) (pinned_ptr va' p).
  Proof.
    rewrite pinned_ptr.unlock.
    iIntros "[%H1 _] [%H2 _] !> !%". congruence.
  Qed.

  Lemma offset_2_pinned_ptr_pure o1 o2 z1 z2 va p :
    eval_offset σ o1 = Some z1 ->
    eval_offset σ o2 = Some z2 ->
    ptr_vaddr (p ,, o1) = Some va ->
    valid_ptr p |-- valid_ptr (p ,, o1) -* valid_ptr (p ,, o2) -*
    [| 0 <= Z.of_N va - z1 + z2 |]%Z **
    [| ptr_vaddr (p ,, o2) = Some (Z.to_N (Z.of_N va - z1 + z2)) |].
  Proof.
    iIntros (He1 He2 Hpin1) "V V1 V2".
    iDestruct (offset_inv_pinned_ptr_pure with "V1") as %[Hle1 Hp]; [done..|].
    iDestruct (offset_pinned_ptr_pure with "V2") as %[Hle2 Hgoal]; [done..|].
    iIntros "!%". by rewrite Z2N.id in Hgoal, Hle2.
  Qed.

  Lemma pinned_ptr_null : |-- pinned_ptr 0 nullptr.
  Proof.
    rewrite pinned_ptr.unlock.
    iFrame (ptr_vaddr_nullptr).
    iApply exposed_ptr_nullptr.
  Qed.

  #[global] Instance pinned_ptr_zero_is_null (p : ptr) :
    Observe [| p = nullptr |] (pinned_ptr 0 p).
  Proof.
    rewrite pinned_ptr.unlock.
    iIntros "[%Heq #E]".
    rewrite -valid_ptr_zero_null //.
    by iApply (exposed_ptr_valid with "E").
  Qed.

  #[global] Instance pinned_ptr_null_is_zero addr :
    Observe [| addr = 0 |]%N (pinned_ptr addr nullptr).
  Proof.
    rewrite pinned_ptr.unlock ptr_vaddr_nullptr.
    apply: (observe_derive_only_provable (Some 0%N = Some addr)); naive_solver.
  Qed.

  Lemma pinned_ptr_same_address pp1 pp2 v :
    same_address pp1 pp2 ->
    exposed_ptr pp2 |-- pinned_ptr v pp1 -* pinned_ptr v pp2.
  Proof.
    rewrite pinned_ptr.unlock.
    by iIntros ((? & -> & ->)%same_address_iff) "$ [%Hp _] !%".
  Qed.

  Lemma offset_pinned_ptr_Z o z va p :
    eval_offset _ o = Some z ->
    valid_ptr (p ,, o) |--
    pinned_ptr va p -*
    pinned_ptr_Z (Z.of_N va + z) (p ,, o).
  Proof.
    rewrite pinned_ptr.unlock.
    iIntros (He) "#V' #(%P & E)".
    iDestruct (offset_pinned_ptr_pure with "V'") as "[$ $]"; [done..|].
    by iApply offset_exposed_ptr.
  Qed.

  Lemma offset_pinned_ptr o z va p :
    eval_offset _ o = Some z ->
    valid_ptr (p ,, o) |--
    pinned_ptr va p -*
    pinned_ptr (Z.to_N (Z.of_N va + z)) (p ,, o).
  Proof.
    iIntros (?) "V P".
    by iDestruct (offset_pinned_ptr_Z with "V P") as "[_ $]".
  Qed.

  Lemma offset_inv_pinned_ptr_Z o z va p :
    eval_offset _ o = Some z ->
    valid_ptr p |--
    pinned_ptr va (p ,, o) -*
    pinned_ptr_Z (Z.of_N va - z) p.
  Proof.
    rewrite pinned_ptr.unlock.
    iIntros (He) "#V #(%P & E)".
    iDestruct (offset_inv_pinned_ptr_pure with "[]") as "-#[$$]"; [done..| |].
    { by iApply (observe with "E"). }
    by iApply offset_inv_exposed_ptr.
  Qed.

  Lemma offset_2_pinned_ptr_Z o1 o2 z1 z2 va p :
    eval_offset σ o1 = Some z1 ->
    eval_offset σ o2 = Some z2 ->
    valid_ptr p |-- valid_ptr (p ,, o1) -* valid_ptr (p ,, o2) -*
    pinned_ptr va (p ,, o1) -*
    pinned_ptr_Z (Z.of_N va - z1 + z2) (p ,, o2).
  Proof.
    rewrite pinned_ptr.unlock.
    iIntros (He1 He2) "V V1 #V2 #(%P & E)".
    iDestruct (offset_2_pinned_ptr_pure with "V V1 V2") as "[$$]"; [done..|].
    by iApply offset2_exposed_ptr.
  Qed.

  Lemma pinned_ptr_aligned_divide va n p :
    pinned_ptr va p ⊢
    [| aligned_ptr n p <-> (n | va)%N |].
  Proof.
    rewrite pinned_ptr.unlock; iIntros "(%P & _) !%".
    exact: pinned_ptr_pure_aligned_divide.
  Qed.

  Lemma pinned_ptr_pure_type_divide_1 va n p ty
    (Hal : align_of ty = Some n) :
    type_ptr ty p ⊢ [| ptr_vaddr p = Some va |] -∗ [| (n | va)%N |].
  Proof.
    rewrite type_ptr_aligned_pure. iIntros "!%".
    exact: pinned_ptr_pure_divide_1.
  Qed.

  Lemma pinned_ptr_type_divide_1 va n p ty
    (Hal : align_of ty = Some n) :
    type_ptr ty p ⊢ pinned_ptr va p -∗ [| (n | va)%N |].
  Proof.
    rewrite pinned_ptr.unlock.
    iIntros "#? #(? & _)". by iApply pinned_ptr_pure_type_divide_1.
  Qed.

  Lemma shift_pinned_ptr_Z_sub ty z va (p1 p2 : ptr) o:
    p1 ,, o_sub _ ty z = p2 ->
    size_of σ ty = Some o ->
        valid_ptr p2 ** pinned_ptr va p1
    |-- pinned_ptr_Z (Z.of_N va + z * Z.of_N o) p2.
  Proof.
    move => <- Eo.
    iIntros "[val pin1]".
    iApply (offset_pinned_ptr_Z with "val") => //.
    by rewrite eval_o_sub Eo //= Z.mul_comm.
  Qed.

  Lemma shift_pinned_ptr_sub ty z va (p1 p2 : ptr) o:
    p1 ,, o_sub _ ty z = p2 ->
    size_of σ ty = Some o ->
        valid_ptr p2 ** pinned_ptr va p1
    |-- pinned_ptr (Z.to_N (Z.of_N va + z * Z.of_N o)) p2.
  Proof.
    iIntros (??) "VP".
    by iDestruct (shift_pinned_ptr_Z_sub with "VP") as "[_ $]".
  Qed.

  Lemma _valid_valid p vt : _valid_ptr vt p |-- valid_ptr p.
  Proof. case: vt => [|//]. exact: strict_valid_valid. Qed.

  Lemma valid_ptr_sub (i j k : Z) p ty vt
    (Hj : (i <= j <= k)%Z) :
    _valid_ptr vt (p ,, o_sub σ ty i) |--
    _valid_ptr vt (p ,, o_sub σ ty k) -* valid_ptr (p ,, o_sub σ ty j).
  Proof.
    destruct (decide (j = k)) as [->|Hne].
    { rewrite -_valid_valid. by iIntros "_ $". }
    rewrite -strict_valid_valid. apply strict_valid_ptr_sub. lia.
  Qed.

  Lemma _valid_ptr_field_sub (i : Z) (p : ptr) ty f vt (Hle : (0 <= i)%Z) :
    _valid_ptr vt (p ,, o_field σ f ,, o_sub σ ty i) |-- _valid_ptr vt (p ,, o_field σ f).
  Proof.
    iIntros "V". case: (decide (i = 0)%Z) Hle => [-> _|Hne Hle].
    - iDestruct (valid_o_sub_size with "V") as %?.
      by rewrite offset_ptr_sub_0.
    - rewrite strict_valid_ptr_field_sub; last by lia.
      case: vt => //. by rewrite strict_valid_valid.
  Qed.

  Lemma o_base_derived_strict p base derived :
    strict_valid_ptr (p ,, o_base σ derived base) |--
    [| p ,, o_base σ derived base ,, o_derived σ base derived = p |].
  Proof.
    rewrite o_base_directly_derives. f_equiv => ?. exact: o_base_derived.
  Qed.

  Lemma o_derived_base_strict p base derived :
    strict_valid_ptr (p ,, o_derived σ base derived) |--
    [| p ,, o_derived σ base derived ,, o_base σ derived base = p |].
  Proof.
    rewrite o_derived_directly_derives. f_equiv => ?. exact: o_derived_base.
  Qed.

  Lemma o_derived_base_type p base derived ty :
    type_ptr ty (p ,, o_derived σ base derived) |--
    [| p ,, o_derived σ base derived ,, o_base σ derived base = p |].
  Proof. rewrite type_ptr_strict_valid. apply (o_derived_base_strict p). Qed.

  (** [_inv] because unlike [type_ptr_o_base] and [type_ptr_o_field_type_ptr],
  this lemma fits the [type_ptr _ (p ,, o) ⊢ type_ptr _ p] schema instead of the
  converse. *)
  Lemma type_ptr_o_derived_inv derived base p :
    class_derives derived [base] ->
    type_ptr (Tnamed derived) (p ,, _derived base derived) |--
    type_ptr (Tnamed base) p.
  Proof.
    iIntros (Hcd) "T".
    iDestruct (o_derived_base_type with "T") as %Hp.
    by rewrite (type_ptr_o_base _ _ _ Hcd) Hp.
  Qed.

  (** [p] is a valid pointer value in the sense of the standard, or
  "standard-valid" (https://eel.is/c++draft/basic.compound#3.1), that is both
  valid (in our sense) and live.

  In particular, [p] is a valid pointer value even when accounting for
  pointer zapping.
  *)
  Definition _valid_live_ptr vt (p : ptr) : mpred :=
    _valid_ptr vt p ∗ live_ptr p.
  Definition valid_live_ptr p : mpred := _valid_live_ptr Relaxed p.
  Definition strict_valid_live_ptr p : mpred := _valid_live_ptr Strict p.

  #[global] Instance tptsto_as_cfractional ty : AsCFractional2 (tptsto ty).
  Proof. solve_as_cfrac. Qed.

  #[global] Instance mdc_path_as_cfractional this mdc :
    AsCFractional1 (mdc_path this mdc).
  Proof. solve_as_cfrac. Qed.

  #[global] Instance tptsto_observe_nonnull t q p v :
    Observe [| p <> nullptr |] (tptsto t q p v).
  Proof.
    apply: observe_intro.
    destruct (decide (p = nullptr)); subst; last by eauto.
    rewrite {1}tptsto_nonnull. exact: bi.False_elim.
  Qed.

  Lemma tptsto_disjoint ty c1 c2 q p v1 v2 :
    tptsto ty (cQp.mk c1 1) p v1 ** tptsto ty (cQp.mk c2 q) p v2 |-- False.
  Proof.
    iIntros "[T1 T2]".
    iDestruct (tptsto_agree with "T1 T2") as %->.
    iCombine "T1 T2" as "T".
    by iDestruct (cfrac_valid_2 with "T") as %?%Qp.not_add_le_l.
  Qed.

  Lemma offset_ptr_congP (p : ptr) o1 o2 :
    offset_congP σ o1 o2 |--
    type_ptr Tbyte (p ,, o1) -*
    type_ptr Tbyte (p ,, o2) -*
    ptr_congP σ (p ,, o1) (p ,, o2).
  Proof.
    iIntros "% T1 T2". rewrite /ptr_congP. iFrame "T1 T2".
    auto using offset_ptr_cong.
  Qed.

  (** *** Just wrappers. *)
  (** We can lift validity entailments through [Observe] (using
  [Observe_mono]. These are not instances, to avoid causing slowdowns in
  proof search. *)
  Lemma observe_strict_valid_valid
    `(Hobs : !Observe (strict_valid_ptr p) P) : Observe (valid_ptr p) P.
  Proof. by rewrite -strict_valid_valid. Qed.

  Lemma observe_type_ptr_strict_valid
    `(Hobs : !Observe (type_ptr ty p) P) : Observe (strict_valid_ptr p) P.
  Proof. by rewrite -type_ptr_strict_valid. Qed.

  Lemma observe_type_ptr_valid_plus_one
    `(Hobs : !Observe (type_ptr ty p) P) : Observe (valid_ptr (p ,, o_sub σ ty 1)) P.
  Proof. by rewrite -type_ptr_valid_plus_one. Qed.

  Lemma type_ptr_valid ty p : type_ptr ty p |-- valid_ptr p.
  Proof. by rewrite type_ptr_strict_valid strict_valid_valid. Qed.

  Lemma type_ptr__valid ty p vt : type_ptr ty p |-- _valid_ptr vt p.
  Proof.
    case: vt.
    apply type_ptr_strict_valid.
    apply type_ptr_valid.
  Qed.

  #[global] Instance type_ptr_size_observe ty p :
    Observe [| is_Some (size_of σ ty) |] (type_ptr ty p).
  Proof. rewrite type_ptr_size. apply _. Qed.

  #[global] Instance valid_ptr_sub_0 (p : ptr) ty :
    HasSize ty ->
    Observe (valid_ptr (p ,, o_sub σ ty 0)) (valid_ptr p).
  Proof. intros. rewrite offset_ptr_sub_0 //. refine _. Qed.
  #[global] Instance type_ptr_sub_0 (p : ptr) ty :
    HasSize ty ->
    Observe (valid_ptr (p ,, o_sub σ ty 0)) (type_ptr ty p).
  Proof.
    intros. by rewrite type_ptr_valid; apply valid_ptr_sub_0.
  Qed.
  #[global] Instance type_ptr_valid_ptr_next (p : ptr) ty (m n : Z) :
    (m = n + 1)%Z ->
    Observe (valid_ptr (p ,, o_sub σ ty m)) (type_ptr ty (p ,, o_sub σ ty n)).
  Proof.
    intros; subst.
    iIntros "X".
    iDestruct (observe (valid_ptr (p ,, o_sub _ _ _ ,, o_sub _ _ _)) with "X") as "z".
    apply observe_type_ptr_valid_plus_one. refine _.
    by rewrite o_sub_sub.
  Qed.

  Lemma same_alloc_refl p : valid_ptr p ⊢ [| same_alloc p p |].
  Proof.
    rewrite valid_ptr_alloc_id same_alloc_iff. iIntros "!%". case; naive_solver.
  Qed.

  Lemma live_has_alloc_id p :
    live_ptr p ⊢ ∃ aid, [| ptr_alloc_id p = Some aid |] ∗ live_alloc_id aid.
  Proof. rewrite /live_ptr; iIntros. case: (ptr_alloc_id p) => /= [aid|]; eauto. Qed.

  #[global] Instance struct_padding_as_fractional p cls : AsCFractional0 (struct_padding p cls).
  Proof. solve_as_cfrac. Qed.
  #[global] Instance struct_padding_valid_observe p q cls : Observe (strict_valid_ptr p) (struct_padding p cls q).
  Proof. rewrite -type_ptr_strict_valid; apply _. Qed.
  #[global] Instance struct_paddingR_valid_observe p q cls : Observe (valid_ptr p) (struct_padding p cls q).
  Proof. rewrite -strict_valid_valid; apply _. Qed.

  #[global] Instance union_padding_as_fractional p cls : AsCFractional1 (union_padding p cls).
  Proof. solve_as_cfrac. Qed.

  #[global] Instance union_padding_strict_valid_observe p q cls i : Observe (strict_valid_ptr p) (union_padding p cls q i).
  Proof. rewrite -type_ptr_strict_valid; apply _. Qed.
  #[global] Instance union_padding_valid_observe p q cls i : Observe (valid_ptr p) (union_padding p cls q i).
  Proof. rewrite -strict_valid_valid; apply _. Qed.

End with_cpp.

Section has_type.
  Context `{cpp_logic} {σ}.

  (** [has_type] *)

  #[global] Instance has_type_knowledge : Knowledge2 has_type_or_undef.
  Proof. rewrite has_type_or_undef_unfold; split; apply _. Qed.
  #[global] Instance has_type_timeless : Timeless2 has_type_or_undef.
  Proof. rewrite has_type_or_undef_unfold; apply _. Qed.

  Lemma has_type_nonptr v ty :
    nonptr_prim_type ty ->
    has_type v ty -|- [| has_type_prop v ty |].
  Proof.
    intros. split'.
    - by rewrite -has_type_has_type_prop.
    - by rewrite -has_type_prop_has_type_noptr.
  Qed.

  Lemma has_type_qual_iff t q x :
    has_type x t -|- has_type x (Tqualified q t).
  Proof.
    by rewrite (has_type_erase_qualifiers t)
      (has_type_erase_qualifiers (Tqualified _ _)).
  Qed.

  Lemma has_type_drop_qualifiers v ty :
    has_type v ty -|- has_type v (drop_qualifiers ty).
  Proof.
    rewrite (has_type_erase_qualifiers (drop_qualifiers _)) erase_drop_qualifiers.
    by rewrite -has_type_erase_qualifiers.
  Qed.

  Lemma has_type_val_related ty v1 v2 :
    val_related ty v1 v2 ->
    has_type v1 ty -|- has_type v2 ty.
  Proof.
    induction 1.
    { done. }
    { by rewrite -!has_type_qual_iff. }
    all: by rewrite !has_type_nonptr ?has_type_prop_raw_bytes_of_val.
  Qed.

  (** [has_type_or_undef] *)

  Definition is_undef (v : val) : bool :=
    if v is Vundef then true else false.

  Lemma has_type_or_undef_undef t : |-- has_type_or_undef Vundef t.
  Proof. rewrite has_type_or_undef_unfold. by iRight. Qed.

  Lemma has_type_or_undef_nonundef t v :
    ~~ is_undef v -> has_type_or_undef v t -|- has_type v t.
  Proof.
    intros. rewrite has_type_or_undef_unfold. split'.
    - iIntros "[$ | %]". by destruct v.
    - iIntros "?". by iLeft.
  Qed.

  Lemma has_type_or_undef_qual_iff t q v :
    has_type_or_undef v t -|- has_type_or_undef v (Tqualified q t).
  Proof.
    by rewrite !has_type_or_undef_unfold -!has_type_qual_iff.
  Qed.

  Lemma has_type_or_undef_val_related ty v1 v2 :
    val_related ty v1 v2 ->
    has_type_or_undef v1 ty |-- has_type_or_undef v2 ty.
  Proof.
    induction 1.
    { done. }
    { by rewrite -!has_type_or_undef_qual_iff. }
    all: rewrite !has_type_or_undef_nonundef//.
    all: by rewrite !has_type_nonptr// has_type_prop_raw_bytes_of_val.
  Qed.
End has_type.

#[global] Notation "'validP<' ty > v" := (has_type v ty%cpp_type)
  (at level 30, ty at level 20, v at level 1, format "validP< ty >  v") : bi_scope.
