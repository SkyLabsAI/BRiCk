(*
 * Copyright (c) 2020-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(**
The "operational" style definitions about C++ pointers.

C++ pointers are subtle to model.
The definitions in this file are based on the C and C++ standards, and
formalizations of their memory object models (see [doc/sphinx/bibliography.rst]).
 *)
Require Import elpi.apps.locker.locker.

Require Import skylabs.prelude.base.
Require Import skylabs.prelude.addr.
Require Import skylabs.prelude.option.
Require Import skylabs.prelude.numbers.

Require Import skylabs.lang.cpp.syntax.
Require Export skylabs.lang.cpp.semantics.types.
Require Export skylabs.lang.cpp.semantics.genv.
Require Export skylabs.lang.cpp.semantics.alloc_id.

(* We only load Iris to declare trivial OFEs over pointers via [leibnizO]. *)
Require Import iris.algebra.ofe.

#[local] Close Scope nat_scope.
#[local] Open Scope Z_scope.
Implicit Types (σ : genv).

Module Type PTRS_SYNTAX_INPUTS.
  Parameter ptr : Set.
  Parameter offset : Set.
  Parameter __offset_ptr : ptr -> offset -> ptr.
  Parameter __o_dot : offset -> offset -> offset.
End PTRS_SYNTAX_INPUTS.

Module Type PTRS_SYNTAX_MIXIN (Import Inputs : PTRS_SYNTAX_INPUTS).
  Structure DOT : Type :=
    { #[canonical=yes] DOT_from : Type
    ; #[canonical=yes] DOT_to :> Type
    ; #[canonical=no] DOT_dot : DOT_from -> offset -> DOT_to }.
  #[global] Arguments DOT_dot {DOT} _ _ : rename, simpl never.
  Canonical Structure DOT_ptr_offset : DOT :=
    {| DOT_from := ptr; DOT_to := ptr; DOT_dot p o := __offset_ptr p o |}.
  Canonical Structure DOT_offset_offset : DOT :=
    {| DOT_from := offset; DOT_to := offset; DOT_dot o1 o2 := __o_dot o1 o2 |}.

  mlock Definition _dot := @DOT_dot.
  #[global] Arguments _dot {DOT} _ _ : rename, simpl never.

  #[global] Notation _offset_ptr := (@_dot DOT_ptr_offset) (only parsing).
  #[global] Notation o_dot := (@_dot DOT_offset_offset) (only parsing).

  #[global] Notation "p ,, o" := (_dot p o)
    (at level 11, left associativity, format "p  ,,  o") : stdpp_scope.
End PTRS_SYNTAX_MIXIN.

Module Type PTRS.
  (** * Pointers.

  This is the abstract model of pointers in C++ — more precisely, of their
  values. Pointers describe paths that might identify objects, which might be
  alive. Hence they must be understood relative to the C++ object model
  (<https://eel.is/c++draft/intro.object>). We also use pointers to represent the
  values of references, even if those are restricted to point to objects or
  functions (<https://eel.is/c++draft/dcl.ref#5>).

  - Not all of our pointers have concrete addresses.
    In C++, pointers to some objects are never created, and typical compilers
    might choose to not store such objects in memory; nevertheless, for
    uniformity our semantics identifies such objects via pointers, but
    our pointers need not represent an address
    (<https://eel.is/c++draft/basic.compound#def:represents_the_address>).
    Function [ptr_vaddr] maps a pointer to the address it represents, if any.
    See also documentation of [tptsto] and [pinned_ptr].
    (Compilers might temporarily store objects elsewhere, but only as a
    semantics-preserving optimization, which we ignore in our model of the C++
    abstract machine).
    That objects (of non-zero size) have constant addresses follows:
    - for C11 (draft N1570), from 6.2.4.2:
      > An object exists, has a constant address^33
      > [33]: The term ‘‘constant address’’ means that two pointers to the object
      constructed at possibly different times will compare equal.
    - for C++, from <https://eel.is/c++draft/intro.object#8>:

      > an object with nonzero size shall occupy one or more bytes of storage

      and <https://eel.is/c++draft/intro.memory#1>:

      > every byte has a unique address.

  Pointers also have an _allocation ID_; the concept does not exist in
  the standard but is used to model provenance in many models of C
  pointers (CompCert, Krebbers, Cerberus, LLVM's twin semantics), sometimes
  under the name of "object ID". Allocation ID of deallocated regions are never
  reused for new regions.
  - C++ objects form a forest of _complete objects_, and subobjects contained
    within (<https://eel.is/c++draft/intro.object#2>).
    All subobjects of the same complete object share the same allocation
    ID.
  - Character array objects can _provide storage_ to other objects.
    (<http://eel.is/c++draft/intro.object#def:provides_storage>)
    In particular, when memory allocators allocate an object [o] out of a
    character array [arr], then [arr] provides storage to [o].
    Following Cerberus, a pointer to [arr] and a pointer to [o] are
    considered as having distinct provenance.

    In Cerberus, pointers with fresh provenances are created by a
    magic [malloc] primitive, which cannot be implemented in C (at least
    because of effective types, as Krebbers explains); in our semantics,
    pointers with fresh provenance are created by [new] operations (see
    [wp_prval_new] axiom).

  From a pointer to an object, one can use offsets to constructs pointers
  to subobjects.

  Our API allows tracking nested objects accurately, matching the C (object)
  memory model (as rendered by Krebbers) and the model mandated by the C++
  standard.

  A simple model is [alloc ID * option address] [SIMPLE_PTRS_IMPL]; a richer
  one is [PTRS_IMPL].
  *)
  Parameter ptr : Set.

  Implicit Type (p : ptr).

  #[global] Declare Instance ptr_eq_dec : EqDecision ptr.

  #[global] Declare Instance ptr_countable : Countable ptr.

  (** C++ provides a distinguished pointer [nullptr] that is *never
      dereferenceable*
      (<https://eel.is/c++draft/basic.compound#3>)
   *)
  Parameter nullptr : ptr.

  (** An invalid pointer, included as a sentinel value. Other pointers might
      be invalid as well; see [_valid_ptr].
   *)
  Parameter invalid_ptr : ptr.

  (* Pointer to a C++ "complete object" with external or internal linkage, or
     to "functions"; even if they are distinct in C/C++ standards (e.g.
     <https://eel.is/c++draft/basic.pre#:object>
     <https://eel.is/c++draft/basic.compound#3.1>), we represent them in the same
     way.

     Since function pointers cannot be offset, offsetting function pointers
     produces [invalid_ptr], but we haven't needed to expose this.
   *)
  (* ^ the address of global variables & functions *)
  Parameter global_ptr :
    translation_unit -> name -> ptr.
    (* Dynamic loading might require adding some abstract [translation_unit_id]. *)
    (* Might need deferring, as it needs designing a [translation_unit_id];
     since loading the same translation unit twice can give different
     addresses. *)

  Axiom global_ptr_nonnull : forall tu o, global_ptr tu o <> nullptr.

  (** * Pointer offsets.
      Offsets represent paths between objects and subobjects.

      If [p] points to an object and [o] is an offset to a subobject,
      [p ,, o] is a pointer to that subobject. If no such object exist,
      [valid_ptr (p ,, o)] will not hold.

      For instance, if [p->x] is a C++ object but [p->y] isn't, in Coq,
      the pointer [p ., o_field "x"] will be valid but [p ., o_field "y"]
      will not.
   *)
  Parameter offset : Set.

  #[global] Declare Instance offset_eq_dec : EqDecision offset.
  #[global] Declare Instance offset_countable : Countable offset.

  (** combine an offset and a pointer to get a new pointer;
    this is a right monoid action.
   *)
  #[local] Parameter __offset_ptr : ptr -> offset -> ptr.
  #[local] Parameter __o_dot : offset -> offset -> offset.

  Include PTRS_SYNTAX_MIXIN.

  (** Offsets form a monoid *)
  Parameter o_id  : offset.

  #[global] Declare Instance id_dot    : LeftId  (=) o_id o_dot.
  #[global] Declare Instance dot_id    : RightId (=) o_id o_dot.
  #[global] Declare Instance dot_assoc : Assoc   (=)      o_dot.

  Axiom offset_ptr_id : forall p : ptr, p ,, o_id = p.
  Axiom offset_ptr_dot : forall (p : ptr) o1 o2,
    p ,, (o1 ,, o2) = p ,, o1 ,, o2.

  (* Other constructors exist, but they are internal to C++ model.
     They include:
     - pointers to local variables (objects with automatic linkage/storage
       duration, <https://eel.is/c++draft/basic.memobj#basic.stc.auto>).
     - pointers to this (<https://eel.is/c++draft/expr.prim.this>) are just normal
       pointers naming the receiver of a method invocation.
   *)

  (** ** Concrete pointer offsets.

      They correspond to the kind of aggregate objects described in e.g.
      <https://eel.is/c++draft/basic.compound>.
   *)

  (* If [p : cls*] points to an object with type [cls] and field [f],
     then [p ,, o_field cls f] points to [p -> f].
   *)
  Parameter o_field : genv -> field -> offset.
  #[global] Arguments o_field _ _%_cpp_field_scope.

  #[global] Notation "p ., o" := (_dot p (o_field _ o))
    (at level 11, left associativity, only parsing) : stdpp_scope.

  (* If [p : cls*] points to an array object with [n] elements and [i ≤ n],
     [p ,, o_sub ty i] represents [p + i] (which might be a past-the-end pointer).
   *)
  Parameter o_sub : genv -> type -> Z -> offset.

  #[global] Notation "p .[ t ! n ]" := (_dot p (o_sub _ t n))
    (at level 11, left associativity, format "p  .[  t  '!'  n  ]") : stdpp_scope.
  #[global] Notation ".[ t ! n ]" := (o_sub _ t n) (at level 11, no associativity, format ".[  t  !  n  ]") : stdpp_scope.

  (** going up and down the class hierarchy, one step at a time;
  these offsets are only for non-virtual inheritance. *)
  Parameter o_base : genv -> forall (derived base : name), offset.
  Parameter o_derived : genv -> forall (base derived : name), offset.

  (* [o_sub_0] axiom is required because any object is a 1-object array
     (<https://eel.is/c++draft/expr.add#footnote-80>).
   *)
  Axiom o_sub_0 : ∀ {σ} ty, is_Some (size_of σ ty) -> .[ty ! 0] = o_id.
  (* TODO: drop (is_Some (size_of σ ty)) via
     `displacement (o_sub σ ty i) = if (i = 0) then 0 else i * size_of σ ty`
   *)
  Axiom o_dot_sub : ∀ {σ} i j ty,
    (o_sub _ ty i) ,, (o_sub _ ty j) = o_sub _ ty (i + j).

  (* We're ignoring virtual inheritance here, since we have no plans to
  support it for now, but this might hold there too. *)
  Axiom o_base_derived : forall σ p base derived,
    directly_derives σ derived base ->
    p ,, o_base σ derived base ,, o_derived σ base derived = p.
  Axiom o_derived_base : forall σ p base derived,
    directly_derives σ derived base ->
    p ,, o_derived σ base derived ,, o_base σ derived base = p.

  (** Map pointers to allocation IDs; total on valid pointers thanks to
      [valid_ptr_alloc_id].
   *)
  Parameter ptr_alloc_id : ptr -> option alloc_id.

  Parameter null_alloc_id : alloc_id.
  Axiom ptr_alloc_id_nullptr :
    ptr_alloc_id nullptr = Some null_alloc_id.

  Axiom ptr_alloc_id_offset : forall {p o},
    is_Some (ptr_alloc_id (p ,, o)) ->
    ptr_alloc_id (p ,, o) = ptr_alloc_id p.
  Axiom global_ptr_nonnull_aid : forall tu o, ptr_alloc_id (global_ptr tu o) <> Some null_alloc_id.

  (** Map pointers to the address they represent,
      (<https://eel.is/c++draft/basic.compound#def:represents_the_address>).
      Not defined on all valid pointers; defined on pointers existing in C++ (
      <https://eel.is/c++draft/basic.compound#3>).
      See discussion above.
   *)
  Parameter ptr_vaddr : ∀ {σ}, ptr -> option vaddr.

  (** [eval_offset] and associated axioms are more advanced, only to be used
  in special cases. *)
  (* TODO drop [genv]. *)
  Parameter eval_offset : genv -> offset -> option Z.

  Section with_genv.
    Context {σ : genv}.

    (** [ptr_vaddr_nullptr] is not mandated by the standard, but valid across
        compilers we are interested in.
        The closest hint is in <https://eel.is/c++draft/conv.ptr>
     *)
    Axiom ptr_vaddr_nullptr : ptr_vaddr nullptr = Some 0%N.

    Axiom global_ptr_nonnull_addr : forall tu o, ptr_vaddr (global_ptr tu o) <> Some 0%N.

    #[global] Declare Instance global_ptr_inj : forall tu, Inj (=) (=) (global_ptr tu).
    #[global] Declare Instance global_ptr_addr_inj : forall tu, Inj (=) (=) (λ o, ptr_vaddr (global_ptr tu o)).
    #[global] Declare Instance global_ptr_aid_inj : forall tu, Inj (=) (=) (λ o, ptr_alloc_id (global_ptr tu o)).

    (** Pointers into the same array with the same address have the same index.
    Wrapped by [same_address_o_sub_eq]. *)
    Axiom ptr_vaddr_o_sub_eq : forall p ty n1 n2 sz,
      size_of σ ty = Some sz -> (sz > 0)%N ->
      same_property ptr_vaddr (p ,, o_sub _ ty n1) (p ,, o_sub _ ty n2) ->
      n1 = n2.

    Axiom eval_o_sub' : forall {ty} {i : Z} sz,
      size_of σ ty = Some sz ->
      (* This order enables reducing for known ty. *)
      eval_offset σ (o_sub σ ty i) = Some (Z.of_N sz * i).

    (**
    To hide implementation details of the compiler from proofs, we restrict
    this axiom to POD/Standard-layout structures.
    *)
    Axiom eval_o_field : forall f n cls st,
      f = Field cls n ->
      glob_def σ cls = Some (Gstruct st) ->
      st.(s_layout) = POD \/ st.(s_layout) = Standard ->
      eval_offset σ (o_field σ f) = offset_of σ cls n.

    (* [eval_offset] respects the monoidal structure of [offset]s _for well-defined offsets_. *)
    Axiom eval_offset_dot : ∀ {o1 o2 s1 s2},
      eval_offset σ o1 = Some s1 ->
      eval_offset σ o2 = Some s2 ->
      eval_offset σ (o1 ,, o2) = Some (s1 + s2).

  End with_genv.
End PTRS.

Module Type PTRS_DERIVED (Import P : PTRS).
  Parameter same_alloc : ptr -> ptr -> Prop.
  Axiom same_alloc_eq : same_alloc = same_property ptr_alloc_id.

  Parameter same_address : ∀ {σ}, ptr -> ptr -> Prop.
  Axiom same_address_eq : ∀ {σ}, same_address = same_property ptr_vaddr.

End PTRS_DERIVED.

Module Type PTRS_DERIVED_MIXIN (Import P : PTRS).
  Definition same_alloc : ptr -> ptr -> Prop := same_property ptr_alloc_id.
  Lemma same_alloc_eq : same_alloc = same_property ptr_alloc_id.
  Proof. done. Qed.

  Definition same_address {σ} : ptr -> ptr -> Prop := same_property ptr_vaddr.
  Lemma same_address_eq {σ} : same_address = same_property ptr_vaddr.
  Proof. done. Qed.

  Definition pinned_ptr_pure {σ} (va : vaddr) (p : ptr) := ptr_vaddr p = Some va.
  Lemma pinned_ptr_pure_eq {σ} :
    pinned_ptr_pure = fun (va : vaddr) (p : ptr) => ptr_vaddr p = Some va.
  Proof. done. Qed.
End PTRS_DERIVED_MIXIN.

(* Double-check [PTRS_DERIVED_MIXIN] matches its interface. *)
Module PTRS_DERIVED_TEST (P : PTRS) : PTRS_DERIVED P.
Include PTRS_DERIVED_MIXIN P.
End PTRS_DERIVED_TEST.

Module Type PTRS_INTF_MINIMAL := PTRS <+ PTRS_DERIVED.

Module Type PTRS_MIXIN (Import P : PTRS_INTF_MINIMAL).
  Implicit Type (p : ptr).

  Notation _id := o_id (only parsing).
  (** access a field *)
  Notation _field := (@o_field _) (only parsing).
  (** subscript an array *)
  Notation _sub z := (@o_sub _ z) (only parsing).
  (** [_base derived base] is a cast from derived to base. *)
  Notation _base := (@o_base _) (only parsing).
  (** [_derived base derived] is a cast from base to derived *)
  Notation _derived := (@o_derived _) (only parsing).

  (**
  Explictly declare that all Iris equalities on pointers are trivial.
  We only add such explicit declarations as actually needed.
  *)
  Canonical Structure ptrO {SI : sidx} := leibnizO ptr.
  #[global] Instance ptr_inhabited : Inhabited ptr := populate nullptr.

  (** ** [offset] Congruence

     [offset_cong σ o1 o2] expresses that [eval_offset σ o1] and [eval_offset σ o2]
     both produce [Some] shared numerical value.

     Given that offsets are typed, [offset_cong] is not generally sufficient to
     transport resources - when the resources are even transportable in the first place.
     However, in certain limited circumstances where the integral values of pointers are
     meaningful - such as reasoning at the level of the byte-representation of an
     object - [offset_cong] becomes a useful way of locally "erasing" the richer structure
     of [ptr]s/[offset]s.

     NOTE: [same_property_iff] ensures that the partial [obs]ervation ([eval_offset])
     are both [Some]; [offset_cong] is [Reflexive] for some [o : offset] iff
     [is_Some (eval_offset σ o)].
   *)
  Definition offset_cong : genv -> relation offset :=
    fun σ o1 o2 => same_property (eval_offset σ) o1 o2.

  (** ** [ptr] Congruence

     [ptr_cong σ p1 p2] expresses that [p1] and [p2] share a common [ptr] prefix and that
     [eval_offset σ o1 o2] holds for the suffixes which "complete" p1 and p2.

     Given that [ptr]s have a rich structure, [ptr_cong σ p1 p2] is not generally sufficient to
     transport resources - when the resources are even transportable in the first place.
     However, in certain limited circumstances where the integral values of pointers are
     meaningful - such as reasoning at the level of the byte-representation of an
     object - [ptr_cong σ p1 p2] (in conjunction with [type_ptr Tbyte p1 ** type_ptr Tbyte p2])
     /can/ be used to transport select resources.
   *)
  Definition ptr_cong : genv -> relation ptr :=
    fun σ p1 p2 =>
      exists p o1 o2,
        p1 = p ,, o1 /\
        p2 = p ,, o2 /\
        offset_cong σ o1 o2.

  Section with_genv.
    Context {σ : genv}.

    Lemma eval_o_sub ty (i : Z) :
      is_Some (size_of σ ty) ->
      eval_offset σ (o_sub σ ty i) =
        (* This order enables reducing for known ty. *)
        (fun n => Z.of_N n * i) <$> size_of σ ty.
    Proof. move => [sz E]. by rewrite (eval_o_sub' sz) //= {}E. Qed.

    Lemma offset_ptr_sub_0 (p : ptr) ty (Hsz : is_Some (size_of σ ty)) :
      p .[ty ! 0] = p.
    Proof. by rewrite o_sub_0 // offset_ptr_id. Qed.

    #[global] Instance offset_cong_equiv : RelationClasses.PER (offset_cong σ).
    Proof. apply same_property_per. Qed.

    Lemma offset_cong_partial_reflexive o :
      is_Some (eval_offset σ o) ->
      offset_cong σ o o.
    Proof. by move /same_property_reflexive_equiv. Qed.

    Lemma offset_cong_offset2 {o1 o2 o3 o4} :
      offset_cong σ o1 o2 ->
      offset_cong σ o3 o4 ->
      offset_cong σ (o1 ,, o3) (o2 ,, o4).
    Proof.
      rewrite /offset_cong !same_property_iff.
      move => [z] [Ho1 Ho2] [z'] [Ho3 Ho4].
      rewrite !(eval_offset_dot (s1 := z) (s2 := z')) //. eauto.
    Qed.

    Lemma offset_cong_offset {o1 o2 o} :
      is_Some (eval_offset σ o) ->
      offset_cong σ o1 o2 ->
      offset_cong σ (o1 ,, o) (o2 ,, o).
    Proof. intros. exact /offset_cong_offset2 /offset_cong_partial_reflexive. Qed.

    Lemma offset_cong_subs {ty1 ty2 : type} {n1 n2 : Z} (sz1 sz2 : N) :
      size_of σ ty1 = Some sz1 ->
      size_of σ ty2 = Some sz2 ->
      (sz1 * n1 = sz2 * n2)%Z ->
      offset_cong σ (.[ ty1 ! n1 ]) (.[ ty2 ! n2 ]).
    Proof.
      move=> Hsz1 Hsz2 E.
      rewrite /offset_cong same_property_iff !eval_o_sub //= Hsz1 Hsz2 /= E.
      eauto.
    Qed.

    #[global] Instance ptr_cong_reflexive : Reflexive (ptr_cong σ).
    Proof.
      red; unfold ptr_cong; intros p; exists p, (.[ Tbyte ! 0 ]), (.[ Tbyte ! 0]).
      intuition; try solve [rewrite offset_ptr_sub_0; auto].
      unfold offset_cong; apply same_property_iff.
      rewrite eval_o_sub //= Z.mul_0_r; eauto.
    Qed.

    #[global] Instance ptr_cong_sym : Symmetric (ptr_cong σ).
    Proof.
      red; unfold ptr_cong.
      intros p p' [p'' [o1 [o2 [Hp [Hp' Hcong]]]]]; subst.
      exists p'', o2, o1. naive_solver.
    Qed.

    (* NOTE (JH): [Transitive] isn't provable without a [ptr_vaddr] side-condition because
       the intermediate [offset] might not [eval_offset] to [Some] integral value.
     *)
    (* #[global] Instance ptr_cong_trans : Transitive (ptr_cong σ). *)

    Lemma offset_ptr_cong (p : ptr) o1 o2 :
      offset_cong σ o1 o2 -> ptr_cong σ (p ,, o1) (p ,, o2).
    Proof. rewrite /ptr_cong. naive_solver. Qed.

    Lemma ptr_cong_offset2 {p1 p2 o1 o2} :
      offset_cong σ o1 o2 ->
      ptr_cong σ p1 p2 ->
      ptr_cong σ (p1 ,, o1) (p2 ,, o2).
    Proof.
      move => Ho12 [p] [o3] [o4] [->] [->] Ho34.
      rewrite -!offset_ptr_dot; eexists _, _, _; split_and! => //.
      exact: (offset_cong_offset2 Ho34 Ho12).
    Qed.

    Lemma ptr_cong_offset {p1 p2 o} :
      is_Some (eval_offset σ o) ->
      ptr_cong σ p1 p2 ->
      ptr_cong σ (p1 ,, o) (p2 ,, o).
    Proof. intros. apply /ptr_cong_offset2 => //. exact: offset_cong_partial_reflexive. Qed.

    Lemma ptr_cong_o_sub {p1 p2 ty i} :
      is_Some (size_of σ ty) ->
      ptr_cong σ p1 p2 ->
      ptr_cong σ (p1 .[ ty ! i ]) (p2 ,, .[ ty ! i ]).
    Proof.
      intros [sz Hsz].
      apply: ptr_cong_offset => //.
      by rewrite eval_o_sub Hsz.
    Qed.

    (** ** [same_address] lemmas *)

    #[global] Instance same_address_dec : RelDecision same_address.
    Proof. rewrite same_address_eq. apply _. Qed.
    #[global] Instance same_address_per : RelationClasses.PER same_address.
    Proof. rewrite same_address_eq. apply _. Qed.
    #[global] Instance same_address_RewriteRelation : RewriteRelation same_address := {}.

    Lemma same_address_iff p1 p2 :
      same_address p1 p2 <-> ∃ va, ptr_vaddr p1 = Some va ∧ ptr_vaddr p2 = Some va.
    Proof. by rewrite same_address_eq same_property_iff. Qed.

    Lemma same_address_intro p1 p2 va :
      ptr_vaddr p1 = Some va -> ptr_vaddr p2 = Some va -> same_address p1 p2.
    Proof. rewrite same_address_eq; exact: same_property_intro. Qed.

    Lemma same_address_nullptr_nullptr : same_address nullptr nullptr.
    Proof. have ? := ptr_vaddr_nullptr. exact: same_address_intro. Qed.

    #[global] Instance ptr_vaddr_proper :
      Proper (same_address ==> eq) ptr_vaddr.
    Proof. by intros p1 p2 (va&->&->)%same_address_iff. Qed.

    #[global] Instance ptr_vaddr_params : Params ptr_vaddr 1 := {}.


    (** ** [same_address_bool] lemmas *)
    Definition same_address_bool p1 p2 := bool_decide (same_address p1 p2).

    #[global] Instance same_address_bool_comm : Comm eq same_address_bool.
    Proof. move=> p1 p2. exact: bool_decide_ext. Qed.

    Lemma same_address_bool_eq {p1 p2 va1 va2} :
      ptr_vaddr p1 = Some va1 → ptr_vaddr p2 = Some va2 →
      same_address_bool p1 p2 = bool_decide (va1 = va2).
    Proof.
      intros Hs1 Hs2. apply bool_decide_ext.
      rewrite same_address_eq same_property_iff. naive_solver.
    Qed.

    Lemma same_address_bool_partial_reflexive p :
      is_Some (ptr_vaddr p) ->
      same_address_bool p p = true.
    Proof.
      move=> Hsm. rewrite /same_address_bool bool_decide_true; first done.
      by rewrite same_address_eq -same_property_reflexive_equiv.
    Qed.

    (** ** [same_alloc] lemmas *)

    #[global] Instance same_alloc_dec : RelDecision same_alloc.
    Proof. rewrite same_alloc_eq. apply _. Qed.
    #[global] Instance same_alloc_per : RelationClasses.PER same_alloc.
    Proof. rewrite same_alloc_eq. apply _. Qed.

    Lemma same_alloc_iff p1 p2 :
      same_alloc p1 p2 <-> ∃ aid, ptr_alloc_id p1 = Some aid ∧ ptr_alloc_id p2 = Some aid.
    Proof. by rewrite same_alloc_eq same_property_iff. Qed.

    Lemma same_alloc_intro p1 p2 aid :
      ptr_alloc_id p1 = Some aid -> ptr_alloc_id p2 = Some aid -> same_alloc p1 p2.
    Proof. rewrite same_alloc_eq; exact: same_property_intro. Qed.

    Lemma same_alloc_nullptr_nullptr : same_alloc nullptr nullptr.
    Proof. have ? := ptr_alloc_id_nullptr. exact: same_alloc_intro. Qed.



    Lemma ptr_alloc_id_base p o
      (Hs : is_Some (ptr_alloc_id (p ,, o))) :
      is_Some (ptr_alloc_id p).
    Proof. by rewrite -(ptr_alloc_id_offset Hs). Qed.

    Lemma same_alloc_offset p o
      (Hs : is_Some (ptr_alloc_id (p ,, o))) :
      same_alloc p (p ,, o).
    Proof.
      case: (Hs) => aid Eq. rewrite same_alloc_iff.
      exists aid. by rewrite -(ptr_alloc_id_offset Hs).
    Qed.

    Lemma same_alloc_offset_2 p o1 o2 p1 p2
      (E1 : p1 = p ,, o1) (E2 : p2 = p ,, o2)
      (Hs1 : is_Some (ptr_alloc_id (p ,, o1)))
      (Hs2 : is_Some (ptr_alloc_id (p ,, o2))) :
      same_alloc p1 p2.
    Proof.
      subst; move: (Hs1) => [aid Eq]; rewrite same_alloc_iff; exists aid; move: Eq.
      by rewrite (ptr_alloc_id_offset Hs1) (ptr_alloc_id_offset Hs2).
    Qed.

    Lemma same_alloc_offset_1 p o
      (Hs : is_Some (ptr_alloc_id (p ,, o))) :
      same_alloc p (p ,, o).
    Proof.
      apply: (same_alloc_offset_2 p o_id o); rewrite ?offset_ptr_id //.
      exact: ptr_alloc_id_base Hs.
    Qed.

    (** Pointers into the same array with the same address have the same index.
    Wrapper by [ptr_vaddr_o_sub_eq]. *)
    Lemma same_address_o_sub_eq p ty n1 n2 sz :
      size_of σ ty = Some sz -> (sz > 0)%N ->
      same_address (p ,, o_sub _ ty n1) (p ,, o_sub _ ty n2) -> n1 = n2.
    Proof. rewrite same_address_eq. exact: ptr_vaddr_o_sub_eq. Qed.

    (** [aligned_ptr] states that the pointer (if it exists in memory) has
    the given alignment.
      *)
    Definition aligned_ptr align p :=
      (exists va, ptr_vaddr p = Some va /\ (align | va)%N) \/ ptr_vaddr p = None.
    Definition aligned_ptr_ty ty p :=
      exists align, align_of ty = Some align /\ aligned_ptr align p.

    Lemma aligned_ptr_ty_erase_qualifiers p ty :
      aligned_ptr_ty ty p <-> aligned_ptr_ty (erase_qualifiers ty) p.
    Proof.
      rewrite /aligned_ptr_ty; intros. by rewrite -align_of_erase_qualifiers.
    Qed.

    #[global] Instance aligned_ptr_divide_mono :
      Proper (flip N.divide ==> eq ==> impl) aligned_ptr.
    Proof.
      move=> m n + _ p ->.
      rewrite /aligned_ptr => ? [[va [P D]]|]; [left|by right].
      eexists _; split=> //. by etrans.
    Qed.
    #[global] Instance aligned_ptr_divide_flip_mono :
      Proper (N.divide ==> eq ==> flip impl) aligned_ptr.
    Proof. solve_proper. Qed.
    #[global] Instance N_divide_RewriteRelation : RewriteRelation N.divide := {}.

    Lemma aligned_ptr_divide_weaken m n p :
      (n | m)%N ->
      aligned_ptr m p -> aligned_ptr n p.
    Proof. by move->. Qed.

    Lemma aligned_ptr_mult_weaken_l m n p :
      aligned_ptr (m * n) p -> aligned_ptr n p.
    Proof. by apply aligned_ptr_divide_weaken, N.divide_mul_r. Qed.

    Lemma aligned_ptr_mult_weaken_r m n p :
      aligned_ptr (m * n) p -> aligned_ptr m p.
    Proof. by apply aligned_ptr_divide_weaken, N.divide_mul_l. Qed.

    Lemma aligned_ptr_min p : aligned_ptr 1 p.
    Proof.
      rewrite /aligned_ptr.
      case: ptr_vaddr; [|by eauto] => va.
      eauto using N.divide_1_l.
    Qed.

    Lemma aligned_ptr_ty_mult_weaken m n ty p :
      align_of ty = Some m -> (n | m)%N ->
      aligned_ptr_ty ty p -> aligned_ptr n p.
    Proof.
      rewrite /aligned_ptr_ty;
        naive_solver eauto using aligned_ptr_divide_weaken.
    Qed.

    Lemma pinned_ptr_pure_aligned_divide va n p :
      ptr_vaddr p = Some va ->
      aligned_ptr n p <-> (n | va)%N.
    Proof. rewrite /aligned_ptr. naive_solver. Qed.

    Lemma pinned_ptr_pure_divide_1 va n p ty
      (Hal : align_of ty = Some n) :
      aligned_ptr_ty ty p → ptr_vaddr p = Some va → (n | va)%N.
    Proof.
      rewrite /aligned_ptr_ty Hal /aligned_ptr /=.
      naive_solver.
    Qed.

    Lemma o_sub_sub (p : ptr) ty i j :
      p .[ ty ! i] .[ty ! j] = p .[ ty ! i + j].
    Proof. by rewrite -offset_ptr_dot o_dot_sub. Qed.

    Lemma o_base_derived_tu `{Hσ : !tu ⊧ σ} p base derived :
      directly_derives_tu tu derived base ->
      p ,, o_base σ derived base ,, o_derived σ base derived = p.
    Proof. intros [??%parent_offset_genv_compat]. exact: o_base_derived. Qed.

    Lemma o_derived_base_tu `{Hσ : !tu ⊧ σ} p base derived :
      directly_derives_tu tu derived base ->
      p ,, o_derived σ base derived ,, o_base σ derived base = p.
    Proof. intros [??%parent_offset_genv_compat]. exact: o_derived_base. Qed.
  End with_genv.

End PTRS_MIXIN.

Module Type PTRS_INTF := PTRS_INTF_MINIMAL <+ PTRS_MIXIN.

