(*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** The "operational" style definitions about C++ values. *)
Require Import Stdlib.Strings.Ascii.
Require Import stdpp.gmap.

Require Import bluerock.prelude.base.
Require Import bluerock.prelude.option.
Require Import bluerock.prelude.numbers.

Require Import bluerock.lang.cpp.reserved_notation. (* TODO *)
Require Import bluerock.prelude.arith.operator.
Require Import bluerock.prelude.arith.builtins.
Require Import bluerock.lang.cpp.syntax.
Require Export bluerock.lang.cpp.semantics.types.
Require Export bluerock.lang.cpp.semantics.sub_module.
Require Export bluerock.lang.cpp.semantics.genv.
Require Export bluerock.lang.cpp.semantics.ptrs.
Require Export bluerock.lang.cpp.semantics.heap_types.

#[local] Set Printing Coercions.
#[local] Close Scope nat_scope.
#[local] Open Scope Z_scope.
Implicit Types (σ : genv).

(* TODO: improve our axiomatic support for raw values - including "shattering"
   non-raw values into their constituent raw pieces - to enable deriving
   [tptsto_ptr_congP_transport] from [tptsto_raw_ptr_congP_transport].
 *)
Module Type RAW_BYTES.
  (** * Raw bytes
      Raw bytes represent the low-level view of data.
      [raw_byte] abstracts over the internal structure of this low-level view of data.
      E.g. in the [simple_pred] model, [raw_byte] would be instantiated with [runtime_val].

      [raw_int_byte] is a raw byte that is a concrete integer values (i.e. not a
      pointer fragment or poison).
   *)
  Parameter raw_byte : Set.
  Parameter raw_byte_eq_dec : EqDecision raw_byte.
  #[global] Existing Instance raw_byte_eq_dec.

  Axiom raw_int_byte : N -> raw_byte.

  (* TODO: refine our treatment of `raw_bytes` s.t. we respect
      the size constraints imposed by the physical hardware.

      The following might help but will likely require other
      axioms which reflect boundedness or round-trip properties.

    [[
    Parameter of_raw_byte : raw_byte -> N.
    Axiom inj_of_raw_byte : Inj (=) (=) of_raw_byte.
    #[global] Existing Instance inj_of_raw_byte.
    ]]
  *)
End RAW_BYTES.

Module Type VAL_MIXIN (Import P : PTRS) (Import R : RAW_BYTES).
  (** * Values
      Primitive abstract C++ runtime values come in two flavors.
      - pointers (also used for references)
      - integers (used for everything else)
      Aggregates are not represented directly, but only by talking about
      primitive subobjects.

      There is also a distinguished undefined element [Vundef] that
      models uninitialized values <https://eel.is/c++draft/basic.indet>.
      Operations on [Vundef] are all undefined behavior.
      [Vraw] (a raw byte) represents the low-level bytewise view of data.
      See [logic/layout.v] for more axioms about it.
  *)
  Variant val : Set :=
  | Vint (_ : Z)
  | Vchar (_ : N)
    (* ^ value used for non-integral character types, e.g.
         [char], [wchar], etc, but *not* [unsigned char] and [signed char]

         The values here are *always* unsigned. When arithmetic is performed
         the semantics will convert the unsigned value into the appropriate
         equivalent on the target platform based on the signedness of the type.
     *)
  | Vptr (_ : ptr)
  | Vraw (_ : raw_byte)
  | Vundef
  | Vmember_ptr (_ : name) (_ : option atomic_name).
  #[global] Notation Vref := Vptr (only parsing).

  (* TODO Maybe this should be removed *)
  #[global] Coercion Vint : Z >-> val.

  Definition val_dec : forall a b : val, {a = b} + {a <> b}.
  Proof. solve_decision. Defined.
  #[global] Instance val_eq_dec : EqDecision val := val_dec.
  #[global] Instance val_inhabited : Inhabited val := populate (Vint 0).

  (** ** Notation wrappers for [val] *)
  Definition Vbool (b : bool) : val :=
    Vint (if b then 1 else 0).
  Definition Vnat (b : nat) : val :=
    Vint (Z.of_nat b).
  Definition Vn (b : N) : val :=
    Vint (Z.of_N b).
  Notation Vz := Vint (only parsing).

  (** we use [Vundef] as our value of type [void] *)
  Definition Vvoid := Vundef.

  (** [is_raw v] holds when [v] is a raw value. *)
  Definition is_raw (v : val) : bool :=
    match v with
    | Vraw _ => true
    | _ => false
    end.

  Definition is_true (v : val) : option bool :=
    match v with
    | Vint v => Some (bool_decide (v <> 0))
    | Vptr p => Some (bool_decide (p <> nullptr))
    | Vchar n => Some (bool_decide (n <> 0%N))
    | Vundef | Vraw _ => None
    | Vmember_ptr _ p => Some (bool_decide (p <> None))
    end.
  #[global] Arguments is_true !_.

  (* An error used to say that [is_true] failed on the value [v] *)
  Record is_true_None (v : val) : Prop := {}.

  Theorem is_true_int : forall i,
      is_true (Vint i) = Some (bool_decide (i <> 0)).
  Proof. reflexivity. Qed.

  Lemma Vptr_inj p1 p2 : Vptr p1 = Vptr p2 -> p1 = p2.
  Proof. by move=> []. Qed.
  Lemma Vint_inj a b : Vint a = Vint b -> a = b.
  Proof. by move=> []. Qed.
  Lemma Vchar_inj a b : Vchar a = Vchar b -> a = b.
  Proof. by move=> []. Qed.
  Lemma Vbool_inj a b : Vbool a = Vbool b -> a = b.
  Proof. by move: a b =>[] [] /Vint_inj. Qed.

  #[global] Instance Vptr_Inj : Inj (=) (=) Vptr := Vptr_inj.
  #[global] Instance Vint_Inj : Inj (=) (=) Vint := Vint_inj.
  #[global] Instance Vchar_Inj : Inj (=) (=) Vchar := Vchar_inj.
  #[global] Instance Vbool_Inj : Inj (=) (=) Vbool := Vbool_inj.

  Definition N_to_char (t : char_type.t) (z : N) : val :=
    Vchar $ trimN (char_type.bitsN t) z.

  (* the default value for a type.
   * this is used to initialize primitives if you do, e.g.
   *   [int x{};]
   *)
  Fixpoint get_default (t : type) : option val :=
    match t with
    | Tptr _ => Some (Vptr nullptr)
    | Tnum _ _ => Some (Vint 0%Z)
    | Tchar_ _ => Some (Vchar 0%N)
    | Tbool => Some (Vbool false)
    | Tnullptr => Some (Vptr nullptr)
    | Tqualified _ t => get_default t
    | _ => None
    end.
End VAL_MIXIN.

Module Type RAW_BYTES_VAL
       (Import P : PTRS) (Import R : RAW_BYTES)
       (Import V : VAL_MIXIN P R).
  (** [raw_bytes_of_val σ ty v rs] states that the value [v] of type
      [ty] is represented by the raw bytes in [rs]. What this means
      depends on the type [ty]. *)
  Parameter raw_bytes_of_val : genv -> Rtype -> val -> list raw_byte -> Prop.

  #[local] Notation PROPER R1 R2 := (
    Proper (R1 ==> eq ==> eq ==> eq ==> R2) raw_bytes_of_val
  ) (only parsing).

  #[global] Declare Instance raw_bytes_of_val_mono : PROPER genv_leq impl.
  #[global] Instance raw_bytes_of_val_flip_mono : PROPER (flip genv_leq) (flip impl).
  Proof. repeat intro. exact: raw_bytes_of_val_mono. Qed.
  #[global] Instance raw_bytes_of_val_flip_proper : PROPER genv_eq iff.
  Proof. intros σ1 σ2 [??]; repeat intro. split; exact: raw_bytes_of_val_mono. Qed.

  Axiom raw_bytes_of_val_unique_encoding : forall {σ ty v rs rs'},
      raw_bytes_of_val σ ty v rs -> raw_bytes_of_val σ ty v rs' -> rs = rs'.

  Axiom raw_bytes_of_val_int_unique_val : forall {σ sz sgn z z' rs},
      raw_bytes_of_val σ (Tnum sz sgn) (Vint z) rs ->
      raw_bytes_of_val σ (Tnum sz sgn) (Vint z') rs ->
      z = z'.

  Axiom raw_bytes_of_val_int_bound : forall {σ sz sgn z rs},
      (**
      NOTE: We only need this for [sz = W8]
      *)
      raw_bytes_of_val σ (Tnum sz sgn) (Vint z) rs ->
      int_rank.bound sz sgn z.

  Axiom raw_bytes_of_val_sizeof : forall {σ ty v rs},
      raw_bytes_of_val σ ty v rs -> size_of σ ty = Some (N.of_nat $ length rs).

  (* TODO Maybe add?
    Axiom raw_bytes_of_val_int : forall σ sz z rs,
        raw_bytes_of_val σ (Tnum sz Unsigned) (Vint z) rs <->
        exists l,
          (_Z_from_bytes (genv_byte_order σ) Unsigned l = z) /\
          rs = raw_int_byte <$> l.
  *)

  Module FieldOrBase.
    (* type for representing direct subobjects
       *Always* qualify this name, e.g. [FieldOrBase.t]
     *)
    Variant t : Set :=
    | Field (_ : atomic_name)
    | Base (_ : globname).

    #[global] Instance t_eq_dec : EqDecision t := ltac:(solve_decision).
    #[global] Declare Instance t_countable : Countable t. (*
      { encode x := encode match x with
                      | Field a => inl a
                      | Base b => inr b
                      end
      ; decode x := (fun x => match x with
                           | inl a => Field a
                           | inr b => Base b
                           end) <$> decode x
      }.
    Next Obligation.
      by destruct x; rewrite /= decode_encode/=.
    Qed. *) (* TODO NAMES *)

  End FieldOrBase.

  (** [raw_bytes_of_struct σ cls rss rs] states that the struct
      consisting of fields of the raw bytes [rss] is represented by the
      raw bytes in [rs].

      [rs] should agree with [rss] on the offsets of the fields.
      This is captured by [raw_offsets].

      It might be possible to make some assumptions about the
      parts of [rs] that represent padding based on the ABI. *)
  Parameter raw_bytes_of_struct :
    genv -> globname -> gmap FieldOrBase.t (list raw_byte) -> list raw_byte -> Prop.

  (** TODO: introduction rules for [raw_bytes_of_struct] *)

  (** *** Elimination rules for [raw_bytes_of_struct] *)

  (** The size of the raw bytes of an object is the size of the object *)
  Axiom raw_bytes_of_struct_wf_size : forall σ cls flds rs,
    raw_bytes_of_struct σ cls flds rs ->
    Some (length rs) = N.to_nat <$> (size_of σ (Tnamed cls)).

  (** The raw bytes in each field is the size of the field *)
  (* TODO: type_of_field
  Axiom raw_bytes_of_struct_wf_field : forall σ cls flds rs,
    raw_bytes_of_struct σ cls flds rs ->
    (forall m mty,
        type_of_field cls m = Some mty ->
        exists bytes, flds !! FieldOrBase.Field m = Some bytes /\
                   Some (length bytes) = N.to_nat <$> (size_of σ mty)).
   *)

  (** The raw bytes in each base is the size of the base *)
  Axiom raw_bytes_of_struct_wf_base : forall σ cls flds rs base bytes,
    raw_bytes_of_struct σ cls flds rs ->
    flds !! FieldOrBase.Base base = Some bytes ->
    Some (length bytes) = N.to_nat <$> (size_of σ $ Tnamed base).

  (** The bytes at the offset are the ones that are referenced by the field *)
  Axiom raw_bytes_of_struct_offset : forall σ cls flds rs m bytes off,
    raw_bytes_of_struct σ cls flds rs ->
    flds !! FieldOrBase.Field m = Some bytes ->
    offset_of σ cls m = Some off ->
    firstn (length bytes) (skipn (Z.to_nat off) rs) = bytes.

End RAW_BYTES_VAL.

Module Type RAW_BYTES_MIXIN
       (Import P : PTRS) (Import R : RAW_BYTES)
       (Import V : VAL_MIXIN P R)
       (Import RD : RAW_BYTES_VAL P R V).

  (**
  The relation [val_related ty] is, for most types [ty], equality on
  values. For type [Tbyte], it also includes the relation between [Vint]
  and [Vraw] induced by [raw_bytes_of_val].

  NOTE: Should we need it, we can show [val_related] to be compatible
  with qualifier normalization ([qual_norm'], [qual_norm],
  [decompose_type], [drop_qualifiers]) and erasure
  ([erase_qualifiers]) up to [iff]. The following, for example, is
  provable.
  <<
    ∀ {σ} ty v1 v2,
    val_related ty v1 v2 <->
    qual_norm (fun _ ty => val_related ty v1 v2) ty
  >>
  We have the option to strengthen that [<->] to [=]
  <<
    ∀ {σ} ty,
    val_related ty =
    qual_norm (fun _ => val_related_unqualified) ty
  >>
  by defining [val_related] using [qual_norm] and an auxiliary
  type-indexed family of relations [val_related_unqualified], rather
  than directly as an inductive.
  *)

  Inductive val_related {σ : genv} : Rtype -> val -> val -> Prop :=
  | Veq_refl ty v : val_related ty v v
  | Vqual t ty v1 v2 :
    val_related ty v1 v2 ->
    val_related (Tqualified t ty) v1 v2
  | Vraw_uint8 raw z (Hraw : raw_bytes_of_val σ Tbyte (Vint z) [raw]) :
    val_related Tbyte (Vraw raw) (Vint z)
  | Vuint8_raw z raw (Hraw : raw_bytes_of_val σ Tbyte (Vint z) [raw]) :
    val_related Tbyte (Vint z) (Vraw raw).
  #[local] Hint Constructors val_related : core.

  Lemma val_related_not_raw {σ} v1 v2 ty :
    ~~ is_raw v1 -> ~~ is_raw v2 ->
    val_related ty v1 v2 -> v1 = v2.
  Proof. intros ??. induction 1; naive_solver. Qed.

  Lemma val_related_Vint' {σ} ty v1 v2 :
    val_related ty v1 v2 ->
    forall z1 z2, v1 = Vint z1 -> v2 = Vint z2 -> z1 = z2.
  Proof.
    induction 1; simpl; intros; subst; eauto; try congruence.
  Qed.
  Lemma val_related_Vint {σ} ty z1 z2 :
    val_related ty (Vint z1) (Vint z2) -> z1 = z2.
  Proof. intros. exact: val_related_Vint'. Qed.

  Lemma val_related_Vchar' {σ} ty v1 v2 :
    val_related ty v1 v2 ->
    forall z1 z2, v1 = Vchar z1 -> v2 = Vchar z2 -> z1 = z2.
  Proof. induction 1; naive_solver. Qed.
  Lemma val_related_Vchar {σ} ty n1 n2 :
    val_related ty (Vchar n1) (Vchar n2) -> n1 = n2.
  Proof. intros. exact: val_related_Vchar'. Qed.

  (*
  NOTE: This stronger property holds because pointers do not have a
  raw representation. (That's future work.).
  *)
  Lemma val_related_Vptr' {σ} ty v1 v2 :
    val_related ty v1 v2 ->
    forall p1, v1 = Vptr p1 -> Vptr p1 = v2.
  Proof. induction 1; naive_solver. Qed.
  Lemma val_related_Vptr {σ} ty p1 v2 :
    val_related ty (Vptr p1) v2 -> Vptr p1 = v2.
  Proof. intros. exact: val_related_Vptr'. Qed.
  Lemma val_related_ptr_iff {σ} ty v1 v2 :
    val_related (Tptr ty) v1 v2 <-> v1 = v2.
  Proof. split. by inversion 1. by intros ->. Qed.

  Lemma val_related_Vundef' {σ} ty v1 v2 :
    val_related ty v1 v2 ->
    v1 = Vundef -> v2 = Vundef.
  Proof. induction 1; naive_solver. Qed.
  Lemma val_related_Vundef {σ} ty v :
    val_related ty Vundef v -> v = Vundef.
  Proof. intros. exact: val_related_Vundef'. Qed.

  Lemma val_related_Vraw' {σ} ty v1 v2 :
    val_related ty v1 v2 ->
    forall r1 r2, v1 = Vraw r1 -> v2 = Vraw r2 -> r1 = r2.
  Proof. induction 1; naive_solver. Qed.
  Lemma val_related_Vraw {σ} ty r1 r2 :
    val_related ty (Vraw r1) (Vraw r2) -> r1 = r2.
  Proof. intros. exact: val_related_Vraw'. Qed.

  Lemma val_related_qual {σ} q ty v1 v2 :
    val_related ty v1 v2 ->
    val_related (Tqualified q ty) v1 v2.
  Proof. by constructor. Qed.

  #[global] Instance val_related_equivalence {σ} ty : Equivalence (val_related ty).
  Proof.
    split; red.
    { done. }
    { induction 1; auto. }
    intros v1 v2. induction 1.
    { done. }
    { inversion 1; simplify_eq; auto. }
    { inversion 1; simplify_eq; auto.
      have [->] := raw_bytes_of_val_unique_encoding Hraw Hraw0. auto. }
    { inversion 1; simplify_eq; auto.
      have -> := raw_bytes_of_val_int_unique_val Hraw Hraw0. auto. }
  Qed.

  #[local] Notation PROPER R1 R2 := (
    Proper (R1 ==> eq ==> eq ==> eq ==> R2) (@val_related)
  ) (only parsing).

  #[global] Instance val_related_mono : PROPER genv_leq impl.
  Proof.
    intros σ1 σ2 Hσ ty?<- v1?<- v2?<-. red. induction 1; auto.
    all: rewrite Hσ in Hraw; auto.
  Qed.
  #[global] Instance val_related_flip_mono : PROPER (flip genv_leq) (flip impl).
  Proof. repeat intro. exact: val_related_mono. Qed.
  #[global] Instance val_related_flip_proper : PROPER genv_eq iff.
  Proof. intros σ1 σ2 [??]; repeat intro. split; exact: val_related_mono. Qed.

  (** TODO: Arguably misplaced *)
  Lemma raw_bytes_of_val_uint_length {σ} v rs sz sgn :
    raw_bytes_of_val σ (Tnum sz sgn) v rs ->
    length rs = int_rank.bytesNat sz.
  Proof.
    move => /raw_bytes_of_val_sizeof/=.
    rewrite /int_rank.bytesN /bitsize.bytesN.
    inversion 1. lia.
  Qed.
End RAW_BYTES_MIXIN.

Module Type HAS_TYPE (Import P : PTRS) (Import R : RAW_BYTES) (Import V : VAL_MIXIN P R).
  (** typedness of values
      note that only primitives fit into this, there is no [val] representation
      of aggregates, except through [Vptr p] with [p] pointing to the contents.
  *)

  (**
  [has_type_prop v ty] is an under-approximation in [Prop] of "[v] is an initialized value
  of type [t]."
  Assuming [ty] isn't qualified, this implies:
  - if [ty <> Tvoid], then [v <> Vundef] in all provable cases <--
    ^---- TODO: <https://gitlab.com/bedrocksystems/cpp2v-core/-/issues/319>.
    See aborted lemma [has_type_prop_not_vundef] below.
  - if [ty = Tvoid], then [v = Vundef].
  - if [ty = Tnullptr], then [v = Vptr nullptr].
  - if [ty = Tnum sz sgn], then [v] fits the appropriate bounds (see
    [has_int_type']).
  - if [ty] is a type of pointers, we only ensure that [v = Vptr p].
  - if [ty] is a type of references, we ensure that [v = Vref p] and
    that [p <> nullptr]; [Vref] is an alias for [Vptr]
  See [has_type] for a stronger version.

  TODO: Currently, [has_type_prop] isn't the maximal pure part of [has_type].
    *)
  Parameter has_type_prop : forall {σ : genv}, val -> Rtype -> Prop.
  #[global] Notation "'valid<' ty > v" := (has_type_prop v ty%cpp_type)
       (at level 30, ty at level 20, v at level 1, format "valid< ty >  v") : type_scope.

  #[global]
  Declare Instance has_type_prop_mono : Proper (genv_leq ==> eq ==> eq ==> Basics.impl) (@has_type_prop).

  #[global]
  Instance has_type_prop_proper : Proper (genv_eq ==> eq ==> eq ==> iff) (@has_type_prop).
  Proof.
    compute; split; apply has_type_prop_mono; eauto; tauto.
  Qed.

  Section with_genv.
    Context {σ : genv}.

    Axiom has_type_prop_pointer : forall v ty,
        has_type_prop v (Tptr ty) <-> exists p, v = Vptr p.
    Axiom has_type_prop_erase_qualifiers : forall v ty,
        has_type_prop v ty <-> has_type_prop v (erase_qualifiers ty).
    Axiom has_type_prop_nullptr : forall v,
        has_type_prop v Tnullptr <-> v = Vptr nullptr.
    Axiom has_type_prop_ref : forall v ty,
        has_type_prop v (Tref ty) <-> exists p, v = Vref p /\ p <> nullptr.
    Axiom has_type_prop_rv_ref : forall v ty,
        has_type_prop v (Trv_ref ty) <-> exists p, v = Vref p /\ p <> nullptr.
    (* TODO FM-3760: the next axioms were not used and have unclear status. *)
    (*
    (* - if [ty] is a type of arrays, we ensure that [v = Vptr p] and
      that [p <> nullptr]. *)
    Axiom has_type_prop_array : forall v ty n,
        has_type_prop v (Tarray ty n) -> exists p, v = Vptr p /\ p <> nullptr.
    Axiom has_type_prop_function : forall v cc rty args,
        has_type_prop v (Tfunction (cc:=cc) rty args) -> exists p, v = Vptr p /\ p <> nullptr.

    (* + NOTE: We require that - for a type [Tnamed nm] - the name resolves to some
      [GlobDecl] other than [Gtype] in a given [σ : genv]. *)
    *)

    Axiom has_type_prop_char : forall ct v,
        (exists n, v = Vchar n /\ 0 <= n < 2^(char_type.bitsN ct))%N <-> has_type_prop v (Tchar_ ct).

    Axiom has_type_prop_void : forall v,
        has_type_prop v Tvoid <-> v = Vvoid.

    Axiom has_type_prop_bool : forall v,
        has_type_prop v Tbool <-> exists b, v = Vbool b.

    (* NOTE: even if an enumeration's underlying type is <<unsigned char>> (which contains
       raw values), raw values are not well typed at the enumeration type. *)
    Axiom has_type_prop_enum : forall v nm,
        has_type_prop v (Tenum nm) <->
        exists tu ty ls,
          tu ⊧ σ /\ tu.(types) !! nm = Some (Genum ty ls) /\
          ~~ is_raw v /\ has_type_prop v (drop_qualifiers ty).

    (** Note in the case of [Tuchar], the value [v] could be a
        raw value. *)
    Axiom has_int_type' : forall sz sgn v,
        has_type_prop v (Tnum sz sgn) <->
          (exists z, v = Vint z /\ bitsize.bound (int_rank.bitsize sz) sgn z) \/
          (exists r, v = Vraw r /\ Tnum sz sgn = Tuchar).

  End with_genv.

End HAS_TYPE.

Module Type HAS_TYPE_MIXIN (Import P : PTRS) (Import R : RAW_BYTES) (Import V : VAL_MIXIN P R)
    (Import HT : HAS_TYPE P R V).
  Section with_env.
    Context {σ : genv}.

    Lemma has_type_prop_qual_iff t q x :
        has_type_prop x t <-> has_type_prop x (Tqualified q t).
    Proof.
      by rewrite (has_type_prop_erase_qualifiers _ (Tqualified _ _))
        (has_type_prop_erase_qualifiers _ t).
    Qed.

    Lemma has_nullptr_type ty :
      has_type_prop (Vptr nullptr) (Tptr ty).
    Proof. by rewrite has_type_prop_pointer; eexists. Qed.

    Lemma has_bool_type : forall z,
      0 <= z < 2 <-> has_type_prop (Vint z) Tbool.
    Proof.
      intros z. rewrite has_type_prop_bool. split=>Hz.
      - destruct (decide (z = 0)); simplify_eq; first by exists false.
        destruct (decide (z = 1)); simplify_eq; first by exists true. lia.
      - unfold Vbool in Hz. destruct Hz as [b Hb].
        destruct b; simplify_eq; lia.
    Qed.

    Lemma has_int_type : forall sz (sgn : signed) z,
        bitsize.bound (int_rank.bitsize sz) sgn z <-> has_type_prop (Vint z) (Tnum sz sgn).
    Proof. move => *. rewrite has_int_type'. naive_solver. Qed.

    Lemma has_type_prop_char' (n : N) ct : (0 <= n < 2 ^ char_type.bitsN ct)%N <-> has_type_prop (Vchar n) (Tchar_ ct).
    Proof. rewrite -has_type_prop_char. naive_solver. Qed.

    Lemma has_type_prop_char_255 (n : N) ct : (0 <= n < 256)%N -> has_type_prop (Vchar n) (Tchar_ ct).
    Proof. intros. rewrite -has_type_prop_char'. destruct ct; simpl; lia. Qed.

    Lemma has_type_prop_char_0 ct : has_type_prop (Vchar 0) (Tchar_ ct).
    Proof. intros. apply has_type_prop_char_255. lia. Qed.

    Lemma has_type_prop_drop_qualifiers :
      forall v ty, has_type_prop v ty <-> has_type_prop v (drop_qualifiers ty).
    Proof.
      induction ty; simpl; eauto.
      by rewrite -has_type_prop_qual_iff -IHty.
    Qed.

    (* TODO fix naming convention *)
    Lemma has_type_prop_qual t q x :
      has_type_prop x (drop_qualifiers t) ->
      has_type_prop x (Tqualified q t).
    Proof.
      intros. by apply has_type_prop_drop_qualifiers.
    Qed.

    (* Not provable yet because our rules are incomplete. *)
    Lemma has_type_prop_not_vundef v ty :
      has_type_prop v ty ->
      drop_qualifiers ty = Tvoid <-> v = Vundef.
    Proof.
      intros Ht%has_type_prop_drop_qualifiers; split; intros E. {
        by rewrite E has_type_prop_void in Ht.
      }
      apply dec_stable => G.
      induction ty; move: Ht => //=. (*
      rewrite has_type_prop_pointer; naive_solver.
      rewrite has_type_prop_ref; naive_solver.
      rewrite has_type_prop_rv_ref; naive_solver.
      rewrite has_int_type'; naive_solver.
      rewrite -has_type_prop_char; naive_solver.
      { (* Needs well-founded induction on types and [genv]! *)
        rewrite has_type_prop_enum => -[?] [?] [?]. }
      rewrite has_type_prop_bool; naive_solver.
      { simpl in G. tauto. }
      rewrite has_type_prop_nullptr; naive_solver.
      all: fail. *)
    Abort.

  End with_env.

  #[global] Hint Resolve has_type_prop_qual : has_type_prop.

  Arguments Z.add _ _ : simpl never.
  Arguments Z.sub _ _ : simpl never.
  Arguments Z.mul _ _ : simpl never.
  Arguments Z.pow _ _ : simpl never.
  Arguments Z.opp _ : simpl never.
  Arguments Z.pow_pos _ _ : simpl never.

End HAS_TYPE_MIXIN.

(* Collect all the axioms. *)
Module Type VALUES_DEFS (P : PTRS_INTF) := RAW_BYTES <+ VAL_MIXIN P <+ RAW_BYTES_VAL P <+ HAS_TYPE P.
(* Plug mixins. *)
Module Type VALUES_INTF_FUNCTOR (P : PTRS_INTF) := VALUES_DEFS P <+ RAW_BYTES_MIXIN P <+ HAS_TYPE_MIXIN P.

Declare Module Export PTRS_INTF_AXIOM : PTRS_INTF.

(* Interface for other modules. *)
Module Export VALUES_INTF_AXIOM <: VALUES_INTF_FUNCTOR PTRS_INTF_AXIOM.
  Include VALUES_INTF_FUNCTOR PTRS_INTF_AXIOM.
End VALUES_INTF_AXIOM.

(** Derived *)

Lemma has_type_prop_raw_bytes_of_val {σ} z raw :
  raw_bytes_of_val σ Tuchar (Vint z) [raw] ->
  has_type_prop (Vraw raw) Tbyte <-> has_type_prop (Vint z) Tbyte.
Proof.
  rewrite !has_int_type'. split.
  { intros [(? & ? & _)|(? & ? & _)]; first done.
    left. eexists; split; first done. exact: raw_bytes_of_val_int_bound. }
  { intros [(? & ? & _)|(? & ? & _)]; last done. right. by eexists. }
Qed.

Lemma has_type_prop_val_related {σ} ty v1 v2 :
  val_related ty v1 v2 ->
  has_type_prop v1 ty <-> has_type_prop v2 ty.
Proof.
  induction 1.
  { done. }
  { by rewrite -!has_type_prop_qual_iff. }
  all: by rewrite has_type_prop_raw_bytes_of_val.
Qed.
