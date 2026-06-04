(*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export elpi.apps.NES.NES.
Require Import stdpp.strings.
Require Export skylabs.prelude.pstring.
Require Import skylabs.lang.cpp.syntax.prelude.
Require Export skylabs.prelude.arith.types.

Require Import Flocq.IEEE754.Binary.
Require Import Flocq.IEEE754.Bits.

(* TODO: is this worth its own file? *)

#[local] Set Primitive Projections.
#[local] Notation EqDecision1 T := (∀ (A : Set), EqDecision A -> EqDecision (T A)) (only parsing).
#[local] Notation EqDecision2 T := (∀ (A : Set), EqDecision A -> EqDecision1 (T A)) (only parsing).
#[local] Notation EqDecision3 T := (∀ (A : Set), EqDecision A -> EqDecision2 (T A)) (only parsing).
#[local] Tactic Notation "solve_decision" := intros; solve_decision.


#[local] Open Scope N_scope.

NES.Begin lang_version.
  Variant t : Set :=
  | Cpp98
  | Cpp03
  | Cpp11
  | Cpp14
  | Cpp17
  | Cpp20
  | Cpp23
  | Cpp26.
  #[only(inhabited,eq_dec)] derive t.

  Definition to_N (v : t) : N :=
    match v with
    | Cpp98 => 1998
    | Cpp03 => 2003
    | Cpp11 => 2011
    | Cpp14 => 2014
    | Cpp17 => 2017
    | Cpp20 => 2020
    | Cpp23 => 2023
    | Cpp26 => 2026
    end%N.

  Definition lt (lhs rhs : t) : bool :=
    bool_decide (to_N lhs < to_N rhs)%N.
NES.End lang_version.

Definition ident : Set := PrimString.string.
Bind Scope pstring_scope with ident.
#[global] Instance ident_eq: EqDecision ident := _.

(** local names
In a normal C++ program, local names are just identifiers but the internal AST
contains two other types of names corresponding to compiler-generated names.
These are:
- opaque names are used for temporaries, e.g. the location that the result of
  <<e>> is placed in in the following code <<auto [a,b] = e>>.
- the names of indicies of array loops, which the AST uses for primitive array
  copies.

NOTE
Because these other types of names occur so infrequently, we choose [PrimString.string] as
the underlying type and use a special prefix for the inaccessible variable names.
 *)
Module localname.
  Definition t : Set := ident.
  #[global] Bind Scope pstring_scope with localname.t.
  #[global] Instance localname_eq: EqDecision t := _.

  (* these are pseudo constructors for making different types
     of local names. *)

  Definition arrayloop_index (n : N) : t :=
    "!" ++ pstring.N.to_string n.
  Definition opaque (n : N) : t :=
    "%" ++ pstring.N.to_string n.
  Definition anon (n : N) : t :=
    "#" ++ pstring.N.to_string n.
End localname.
#[global] Bind Scope pstring_scope with localname.t.
Notation localname := localname.t.

(** * Type Preliminaries *)

(** ** Type qualifiers *)
Variant type_qualifiers : Set :=
| QCV (* const volatile *)
| QC (* const *)
| QV (* volatile *)
| QM (* no qualifiers *)
.
#[only(inhabited,eq_dec,countable)] derive type_qualifiers.

Definition q_const (q : type_qualifiers) : bool :=
  match q with
  | QCV | QC => true
  | _ => false
  end.
Definition q_volatile (q : type_qualifiers) : bool :=
  match q with
  | QCV | QV => true
  | _ => false
  end.
Definition CV (const volatile : bool) :=
  match const , volatile with
  | true , true => QCV
  | true , false => QC
  | false , true => QV
  | false , false => QM
  end.

(* [merge_tq a b] computes the join of the restrictions of [a] and [b],
   i.e. if either [a] or [b] is const/volatile, the result will be const/volatile.
   This is used to compress adjacent qualifiers.
 *)
Definition merge_tq (a b : type_qualifiers) : type_qualifiers :=
  CV (q_const a || q_const b) (q_volatile a || q_volatile b).

#[global] Instance merge_tq_idemp : IdemP (=) merge_tq.
Proof. by intros []. Qed.
#[global] Instance merge_tq_left_id : LeftId (=) QM merge_tq.
Proof. by intros []. Qed.
#[global] Instance merge_tq_right_id : RightId (=) QM merge_tq.
Proof. by intros []. Qed.
#[global] Instance merge_tq_left_absorb : LeftAbsorb (=) QCV merge_tq.
Proof. by intros []. Qed.
#[global] Instance merge_tq_right_absorb : RightAbsorb (=) QCV merge_tq.
Proof. by intros []. Qed.
#[global] Instance merge_tq_comm : Comm (=) merge_tq.
Proof. by intros [] []. Qed.
#[global] Instance merge_tq_assoc : Assoc (=) merge_tq.
Proof. by intros [] [] []. Qed.

Lemma merge_tq_QM_inj q1 q2 : merge_tq q1 q2 = QM -> q1 = QM /\ q2 = QM.
Proof. destruct q1, q2; naive_solver. Qed.

(**
The preorder from
<https://eel.is/c++draft/basic.type.qualifier#5>
*)
Definition tq_le (a b : type_qualifiers) : Prop :=
  ∃ c, b = merge_tq a c.

Definition is_tq_le (a b : type_qualifiers) : bool :=
  bool_decide (a = b) ||
  match a , b with
  | QM , _ => true
  | QC , QCV => true
  | QV , QCV => true
  | _, _ => false
  end.

Lemma tq_le_is_tq_le a b : tq_le a b <-> is_tq_le a b.
Proof.
  split.
  { intros (c & ->). by destruct a, c. }
  { rewrite /is_tq_le=>?. case_bool_decide.
    - subst a. exists QM. by destruct b.
    - destruct a, b; first [ done | by exists QV | by exists QC | by exists QCV ]. }
Qed.

#[global] Instance tq_le_dec : RelDecision tq_le.
Proof.
  refine (fun a b => cast_if (decide (is_tq_le a b))).
  all: abstract (by rewrite tq_le_is_tq_le).
Defined.

(** ** Calling Conventions *)

(* Calling conventions are a little bit beyond what is formally blessed by
   C++, but the are necessary for low level code that links with other
   languages.

   From the C++ standard point of view, we view these as opaque symbols with
   no particular meaning. All that matters is that when you call a function,
   that this calling convention matches between the caller and the callee.
   This is what ensures, for example, that when you call a function implemented
   in another language, that you have the appropriate annotations in place.
   For example, if you were calling an OpenCL kernel, then the function would
   have type [Tfunction (cc:=CC_OpenCLKernel) ..], and you would require that
   annotation in your program.
 *)
Variant calling_conv : Set :=
| CC_C
| CC_MsAbi
| CC_RegCall.
#[only(inhabited,eq_dec,countable)] derive calling_conv.

(* in almost all contexts, we are going to use [CC_C], so we're going to make
   that the default. Clients interested in specifying another calling convention
   should write, e.g., [Tfunction (cc:=CC_RegCall) ..] to specify the
   calling convention explicitly.
 *)
Existing Class calling_conv.
#[global] Existing Instance CC_C.

(** ** Function Arities, i.e. variadic functions or not *)

Variant function_arity : Set :=
| Ar_Definite
| Ar_Variadic.
#[only(inhabited,eq_dec,countable)] derive function_arity.

(* In almost all contexts, we will use [Ar_Definite], so that is the default. *)
Existing Class function_arity.
#[global] Existing Instance Ar_Definite.

(** ** Character types
    See <https://en.cppreference.com/w/cpp/language/types>
 *)
Module char_type.
  Variant t : Set :=
    | Cchar (* signedness defined by platform *)
    | Cwchar (* signedness defined by platform *)
    | C8 (* unsigned *)
    | C16 (* unsigned *)
    | C32. (* unsigned *)
  #[global] Instance t_eq_dec: EqDecision t.
  Proof. solve_decision. Defined.
  #[global] Instance t_countable : Countable t.
  Proof.
    apply (inj_countable'
      (λ cc,
        match cc with
        | Cchar => 0 | Cwchar => 1 | C8 => 2 | C16 => 3 | C32 => 4
        end)
      (λ n,
        match n with
        | 0 => Cchar | 1 => Cwchar | 2 => C8 | 3 => C16 | 4 => C32
        | _ => Cchar	(** dummy *)
        end)).
    abstract (by intros []).
  Defined.

  Definition bytesN (t : t) : N :=
    match t with
    | Cchar => 1
    | Cwchar => 4 (* TODO: actually 16-bits on Windows *)
    | C8 => 1
    | C16 => 2
    | C32 => 4
    end.
  #[global] Arguments bytesN !_ /.

  Definition bitsN (t : t) : N :=
    8 * bytesN t.
  #[global] Arguments bitsN !_ /.

  #[global] Notation bitsZ t := (Z.of_N (bitsN t)).

End char_type.
Notation char_type := char_type.t.

(** ** Integer types
    See <https://en.cppreference.com/w/cpp/language/types>
 *)
Module int_rank.
  (* the rank <https://eel.is/c++draft/conv.rank> *)
  Variant t : Set :=
  | Ichar
  | Ishort
  | Iint
  | Ilong
  | Ilonglong
  | I128.
  #[global] Instance t_inh : Inhabited t.
  Proof. repeat constructor. Qed.
  #[global] Instance t_eq_dec : EqDecision t.
  Proof. solve_decision. Defined.
  Notation rank := t (only parsing).
  #[global] Instance t_countable : Countable t.
  Proof.
    apply (inj_countable'
             (λ cc,
               match cc with
               | Ichar => 1 | Ishort => 2 | Iint => 3 | Ilong => 4 | Ilonglong => 5 | I128 => 6
               end%positive)
             (λ n,
               match n with
               | 1 => Ichar | 2 => Ishort | 3 => Iint | 4 => Ilong | 5 => Ilonglong
               | _ => I128	(** dummy *)
               end%positive)).
    abstract (by intros []).
  Defined.

  (* all of the ranks ordered from smallest to largest *)
  Definition ranks :=
    [Ichar; Ishort; Iint; Ilong; Ilonglong; I128].

  Definition bitsize (t : t) : bitsize :=
    match t with
    | Ichar => bitsize.W8
    | Ishort => bitsize.W16
    | Iint => bitsize.W32
    | Ilong => bitsize.W64 (* NOTE *)
    | Ilonglong => bitsize.W64
    | I128 => bitsize.W128
    end.

  (* Having this definition not contain multiplication is helpful *)
  Definition bytesN (t : t) : N :=
    match t with
    | Ichar => Evaluate (bitsize.bytesN $ bitsize Ichar)
    | Ishort  => Evaluate (bitsize.bytesN $ bitsize Ishort)
    | Iint  => Evaluate (bitsize.bytesN $ bitsize Iint)
    | Ilong  => Evaluate (bitsize.bytesN $ bitsize Ilong)
    | Ilonglong  => Evaluate (bitsize.bytesN $ bitsize Ilonglong)
    | I128  => Evaluate (bitsize.bytesN $ bitsize I128)
    end.
  Lemma bytesN_ok (t : t) :
    bytesN t = bitsize.bytesN (bitsize t).
  Proof. by destruct t. Qed.

  Notation bytesNat t := (N.to_nat (bytesN t)) (only parsing).
  Lemma bytesNat_ok (t : t) :
    bytesNat t = bitsize.bytesNat (bitsize t).
  Proof. by destruct t. Qed.

  Definition bitsN (t : t) : N :=
    match t with
    | Ichar => Evaluate (8 * bytesN Ichar)
    | Ishort => Evaluate (8 * bytesN Ishort)
    | Iint => Evaluate (8 * bytesN Iint)
    | Ilong => Evaluate (8 * bytesN Ilong)
    | Ilonglong => Evaluate (8 * bytesN Ilonglong)
    | I128 => Evaluate (8 * bytesN I128)
    end.

  #[global] Notation bitsZ t := (Z.of_N (bitsN t)).

  Definition t_leb (a b : t) : bool :=
    match a , b with
    | Ichar , _ => true
    | Ishort , Ichar => false
    | Ishort , _ => true
    | Iint , (Ichar | Ishort) => false
    | Iint , _ => true
    | Ilong , (Ichar | Ishort | Iint) => false
    | Ilong , _ => true
    | Ilonglong , (Ilonglong | I128) => true
    | Ilonglong , _ => false
    | I128 , I128 => true
    | _ , _ => false
    end.
  Definition t_le (a b : t) : Prop :=
    t_leb a b.

  #[global] Instance t_le_dec : RelDecision t_le :=
    ltac:(rewrite /RelDecision; refine _).

  (* [max] on the rank. *)
  Definition t_max (a b : t) : t :=
    if bool_decide (t_le a b) then b else a.

  #[global] Notation max_val sz := (bitsize.max_val (bitsize sz)) (only parsing).
  #[global] Notation min_val sz := (bitsize.min_val (bitsize sz)) (only parsing).
  #[global] Notation bound sz  := (bitsize.bound (bitsize sz))   (only parsing).

End int_rank.
Notation int_rank := int_rank.t.
#[deprecated(since="2024-06-22",note="use [int_rank].")]
Notation int_type := int_rank.t (only parsing).
#[global] Arguments int_rank.bytesN !_ /.
#[global] Arguments int_rank.bitsN !_ /.
(* #[global] Arguments int_rank.bitsize !_ /. TODO: do I want this? *)

Module integral_type.
  Record t : Set := mk { size : int_rank.t ; signedness : signed }.
End integral_type.
(** ** Floating point types
    See <https://en.cppreference.com/w/cpp/language/types>
 *)
Module float_type.
  Variant t : Set :=
    | Ffloat16
    | Ffloat
    | Fdouble
    | Flongdouble
    | Ffloat128.

  #[global] Instance t_eq_dec : EqDecision t := ltac:(solve_decision).
  #[global] Instance t_countable : Countable t.
  Proof.
    apply (inj_countable'
      (λ cc,
        match cc with
        | Ffloat16 => 3 | Ffloat => 0 | Fdouble => 1 | Flongdouble => 2 | Ffloat128 => 4
        end)
      (λ n,
        match n with
        | 0 => Ffloat | 1 => Fdouble | 2 => Flongdouble | 3 => Ffloat16 | 4 => Ffloat128
        | _ => Ffloat	(** dummy *)
        end)).
    abstract (by intros []).
  Defined.

  Definition bytesN (t : t) : N :=
    match t with
    | Ffloat16 => 2
    | Ffloat => 4
    | Fdouble => 8
    | Flongdouble => 16
    | Ffloat128 => Evaluate (128 / 8)%N
    end.

  Definition bitsN (t : t) : N :=
    8 * bytesN t.

  (** Parameters for [binary_float].

      [mw] is the significand precision, including the implicit leading bit
      for normalized finite values. [ew] is the exponent bound parameter used
      by [binary_float].
   *)
  Definition mw (t : t) : Z :=
    match t with
    | Ffloat16 => 11
    | Ffloat => 24
    | Fdouble => 53
    | Flongdouble => 64
    | Ffloat128 => 113
    end.

  Lemma mw_gt_0 (t : t) : (0 < mw t)%Z.
  Proof. by destruct t. Qed.

  Definition ew (t : t) : Z :=
    match t with
    | Ffloat16 => 16
    | Ffloat => 128
    | Fdouble => 1024
    | Flongdouble => 16384
    | Ffloat128 => 16384
    end.

  Lemma mw_lt_ew (t : t) : (mw t < ew t)%Z.
  Proof. by destruct t. Qed.


  (** Parameters for the IEEE bit encoding helpers.

      Flocq's [binary_float] uses the full significand precision [mw],
      including the implicit leading bit for normal finite values, while its
      bit-conversion helpers take the number of stored fraction bits. Thus the
      first bit-conversion parameter is [mw - 1].

      The [binary_float] exponent parameter is [2 ^ (ebits - 1)], so the
      stored exponent width is recovered from [ew].
   *)
  Definition fraction_bits (t : t) : Z := mw t - 1.
  Definition exponent_bits (t : t) : Z := Z.log2 (ew t) + 1.

  (** The carrier type *)
  Definition car (t : t) : Set :=
    binary_float (mw t) (ew t).

  #[global] Instance full_float_dec : EqDecision full_float.
  Proof. red. intros. red. decide equality; try (apply decide; refine _). Defined.

  #[global] Instance car_dec {ft : t} : EqDecision (car ft) :=
    fun a b =>
      match decide (B2FF _ _ a = B2FF _ _ b) with
      | left pf => left (B2FF_inj _ _ _ _ pf)
      | right pf => right (fun x => pf match x in _ = X return B2FF _ _ _ = B2FF _ _ X with
                                  | eq_refl => eq_refl
                                  end)
      end.

End float_type.
Notation float_type := float_type.t.

Module float_value.
  Import float_type.

  (** Build a floating-point value from the usual IEEE sign/exponent/fraction
      bit encoding, interpreted as a non-negative [Z].

      [Flongdouble] is included to keep the function total, but cpp2v should
      only use this helper when Clang's [APFloat] layout matches this implicit
      leading-bit encoding. In particular, x87 long double has an explicit
      integer bit and is not printed through this path. *)
  Definition of_bits (t : t) : Z -> car t :=
    match t with
    | Ffloat16 => binary_float_of_bits (Reduce (fraction_bits Ffloat16)) (Reduce (exponent_bits Ffloat16)) eq_refl eq_refl eq_refl
    | Ffloat => binary_float_of_bits (Reduce (fraction_bits Ffloat)) (Reduce (exponent_bits Ffloat)) eq_refl eq_refl eq_refl
    | Fdouble => binary_float_of_bits (Reduce (fraction_bits Fdouble)) (Reduce (exponent_bits Fdouble)) eq_refl eq_refl eq_refl
    | Flongdouble => binary_float_of_bits (Reduce (fraction_bits Flongdouble)) (Reduce (exponent_bits Flongdouble)) eq_refl eq_refl eq_refl
    | Ffloat128 => binary_float_of_bits (Reduce (fraction_bits Ffloat128)) (Reduce (exponent_bits Ffloat128)) eq_refl eq_refl eq_refl
    end.

  Definition to_bits (t : t) : car t -> Z :=
    match t with
    | Ffloat16 => bits_of_binary_float (Reduce (fraction_bits Ffloat16)) (Reduce (exponent_bits Ffloat16))
    | Ffloat => bits_of_binary_float (Reduce (fraction_bits Ffloat)) (Reduce (exponent_bits Ffloat))
    | Fdouble => bits_of_binary_float (Reduce (fraction_bits Fdouble)) (Reduce (exponent_bits Fdouble))
    | Flongdouble => bits_of_binary_float (Reduce (fraction_bits Flongdouble)) (Reduce (exponent_bits Flongdouble))
    | Ffloat128 => bits_of_binary_float (Reduce (fraction_bits Ffloat128)) (Reduce (exponent_bits Ffloat128))
    end.

  Definition zero (t : t) : car t :=
    B754_zero _ _ false.

  Definition signed_zero (t : t) : bool -> car t :=
    B754_zero _ _.

  Definition is_zero [t : t] (v : car t) : bool :=
    match v with
    | B754_zero _ _ _ => true
    | _ => false
    end.

  Definition default_nan (t : t) : { nan : car t | is_nan _ _ nan = true } :=
    match t return { nan : car t | is_nan _ _ nan = true } with
    | Ffloat16 => exist _ (@B754_nan 11 16 false xH eq_refl) eq_refl
    | Ffloat => exist _ (@B754_nan 24 128 false xH eq_refl) eq_refl
    | Fdouble => exist _ (@B754_nan 53 1024 false xH eq_refl) eq_refl
    | Flongdouble => exist _ (@B754_nan 64 16384 false xH eq_refl) eq_refl
    | Ffloat128 => exist _ (@B754_nan 113 16384 false xH eq_refl) eq_refl
    end.

  Definition unop_nan [t : t] (v : car t) : { nan : car t | is_nan _ _ nan = true } :=
    match v with
    | B754_nan _ _ s pl Hpl => exist _ (B754_nan _ _ s pl Hpl) eq_refl
    | _ => default_nan t
    end.

  Definition binop_nan [t : t] (v1 v2 : car t) : { nan : car t | is_nan _ _ nan = true } :=
    match v1, v2 with
    | B754_nan _ _ s pl Hpl, _ => exist _ (B754_nan _ _ s pl Hpl) eq_refl
    | _, B754_nan _ _ s pl Hpl => exist _ (B754_nan _ _ s pl Hpl) eq_refl
    | _, _ => default_nan t
    end.


  Definition opp (t : t) (v : car t) : car t :=
    Bopp _ _ (@unop_nan t) v.

  Definition normalize_with_mode (m : BinarySingleNaN.mode) (t : t) (z e : Z) (signed_zero : bool) : car t :=
    match t return car t with
    | Ffloat16 => binary_normalize _ _ (mw_gt_0 Ffloat16) (mw_lt_ew Ffloat16) m z e signed_zero
    | Ffloat => binary_normalize _ _ (mw_gt_0 Ffloat) (mw_lt_ew Ffloat) m z e signed_zero
    | Fdouble => binary_normalize _ _ (mw_gt_0 Fdouble) (mw_lt_ew Fdouble) m z e signed_zero
    | Flongdouble => binary_normalize _ _ (mw_gt_0 Flongdouble) (mw_lt_ew Flongdouble) m z e signed_zero
    | Ffloat128 => binary_normalize _ _ (mw_gt_0 Ffloat128) (mw_lt_ew Ffloat128) m z e signed_zero
    end.

  Definition normalize (t : t) (z e : Z) (signed_zero : bool) : car t :=
    normalize_with_mode BinarySingleNaN.mode_NE t z e signed_zero.

  Definition of_int_with_mode (m : BinarySingleNaN.mode) (t : t) (z : Z) : car t :=
    normalize_with_mode m t z 0 false.

  Definition of_int (t : t) (z : Z) : car t :=
    of_int_with_mode BinarySingleNaN.mode_NE t z.

  Definition to_int (t : t) (v : car t) : option Z :=
    match v with
    | B754_zero _ _ _ => Some 0%Z
    | B754_finite _ _ s m e _ =>
        let mag :=
          if (0 <=? e)%Z then Z.shiftl (Zpos m) e else Z.shiftr (Zpos m) (- e)
        in
        Some (if s then (- mag)%Z else mag)
    | _ => None
    end.

  Definition cast_with_mode (m : BinarySingleNaN.mode) (from to : t) (v : car from) : option (car to) :=
    Some
      match v with
      | B754_zero _ _ s => signed_zero to s
      | B754_infinity _ _ s => B754_infinity _ _ s
      | B754_nan _ _ _ _ _ => proj1_sig (default_nan to)
      | B754_finite _ _ s m' e _ =>
          normalize_with_mode m to (if s then (- Zpos m')%Z else Zpos m') e false
      end.

  Definition cast (from to : t) : car from -> option (car to) :=
    cast_with_mode BinarySingleNaN.mode_NE from to.

  Definition add_with_mode (m : BinarySingleNaN.mode) (t : t) : car t -> car t -> car t :=
    match t return car t -> car t -> car t with
    | Ffloat16 => Bplus _ _ (mw_gt_0 Ffloat16) (mw_lt_ew Ffloat16) (@binop_nan Ffloat16) m
    | Ffloat => Bplus _ _ (mw_gt_0 Ffloat) (mw_lt_ew Ffloat) (@binop_nan Ffloat) m
    | Fdouble => Bplus _ _ (mw_gt_0 Fdouble) (mw_lt_ew Fdouble) (@binop_nan Fdouble) m
    | Flongdouble => Bplus _ _ (mw_gt_0 Flongdouble) (mw_lt_ew Flongdouble) (@binop_nan Flongdouble) m
    | Ffloat128 => Bplus _ _ (mw_gt_0 Ffloat128) (mw_lt_ew Ffloat128) (@binop_nan Ffloat128) m
    end.

  Definition sub_with_mode (m : BinarySingleNaN.mode) (t : t) : car t -> car t -> car t :=
    match t return car t -> car t -> car t with
    | Ffloat16 => Bminus _ _ (mw_gt_0 Ffloat16) (mw_lt_ew Ffloat16) (@binop_nan Ffloat16) m
    | Ffloat => Bminus _ _ (mw_gt_0 Ffloat) (mw_lt_ew Ffloat) (@binop_nan Ffloat) m
    | Fdouble => Bminus _ _ (mw_gt_0 Fdouble) (mw_lt_ew Fdouble) (@binop_nan Fdouble) m
    | Flongdouble => Bminus _ _ (mw_gt_0 Flongdouble) (mw_lt_ew Flongdouble) (@binop_nan Flongdouble) m
    | Ffloat128 => Bminus _ _ (mw_gt_0 Ffloat128) (mw_lt_ew Ffloat128) (@binop_nan Ffloat128) m
    end.

  Definition mul_with_mode (m : BinarySingleNaN.mode) (t : t) : car t -> car t -> car t :=
    match t return car t -> car t -> car t with
    | Ffloat16 => Bmult _ _ (mw_gt_0 Ffloat16) (mw_lt_ew Ffloat16) (@binop_nan Ffloat16) m
    | Ffloat => Bmult _ _ (mw_gt_0 Ffloat) (mw_lt_ew Ffloat) (@binop_nan Ffloat) m
    | Fdouble => Bmult _ _ (mw_gt_0 Fdouble) (mw_lt_ew Fdouble) (@binop_nan Fdouble) m
    | Flongdouble => Bmult _ _ (mw_gt_0 Flongdouble) (mw_lt_ew Flongdouble) (@binop_nan Flongdouble) m
    | Ffloat128 => Bmult _ _ (mw_gt_0 Ffloat128) (mw_lt_ew Ffloat128) (@binop_nan Ffloat128) m
    end.

  Definition div_with_mode (m : BinarySingleNaN.mode) (t : t) : car t -> car t -> car t :=
    match t return car t -> car t -> car t with
    | Ffloat16 => Bdiv _ _ (mw_gt_0 Ffloat16) (mw_lt_ew Ffloat16) (@binop_nan Ffloat16) m
    | Ffloat => Bdiv _ _ (mw_gt_0 Ffloat) (mw_lt_ew Ffloat) (@binop_nan Ffloat) m
    | Fdouble => Bdiv _ _ (mw_gt_0 Fdouble) (mw_lt_ew Fdouble) (@binop_nan Fdouble) m
    | Flongdouble => Bdiv _ _ (mw_gt_0 Flongdouble) (mw_lt_ew Flongdouble) (@binop_nan Flongdouble) m
    | Ffloat128 => Bdiv _ _ (mw_gt_0 Ffloat128) (mw_lt_ew Ffloat128) (@binop_nan Ffloat128) m
    end.

  (** We fix the rounding mode, we will not support this changing a runtime for the time
      being because that would introduce differences between compile time and runtime evaluation.
   *)
  Definition add (t : t) : car t -> car t -> car t := add_with_mode BinarySingleNaN.mode_NE t.
  Definition sub (t : t) : car t -> car t -> car t := sub_with_mode BinarySingleNaN.mode_NE t.
  Definition mul (t : t) : car t -> car t -> car t := mul_with_mode BinarySingleNaN.mode_NE t.
  Definition div (t : t) : car t -> car t -> car t := div_with_mode BinarySingleNaN.mode_NE t.

  Definition value_compare (t : t) : car t -> car t -> option comparison :=
    match t return car t -> car t -> option comparison with
    | Ffloat16 => Bcompare _ _
    | Ffloat => Bcompare _ _
    | Fdouble => Bcompare _ _
    | Flongdouble => Bcompare _ _
    | Ffloat128 => Bcompare _ _
    end.

  Definition eqb (t : t) (v1 v2 : car t) : bool :=
    match value_compare t v1 v2 with
    | Some Eq => true
    | _ => false
    end.

  Definition neqb (t : t) (v1 v2 : car t) : bool :=
    negb (eqb t v1 v2).

  Definition ltb (t : t) (v1 v2 : car t) : bool :=
    match value_compare t v1 v2 with
    | Some Lt => true
    | _ => false
    end.

  Definition leb (t : t) (v1 v2 : car t) : bool :=
    match value_compare t v1 v2 with
    | Some Lt | Some Eq => true
    | _ => false
    end.

  Definition gtb (t : t) (v1 v2 : car t) : bool :=
    ltb t v2 v1.

  Definition geb (t : t) (v1 v2 : car t) : bool :=
    leb t v2 v1.

End float_value.

(** * Expression Preliminaries *)

(** Overloadable operators
    TODO: merge the different operator setups!
 *)
Variant OverloadableOperator : Set :=
  (* Unary operators *)
  | OOTilde | OOExclaim
  | OOPlusPlus | OOMinusMinus
  (* Unary & Binary operators *)
  | OOStar | OOPlus | OOMinus
  (* Binary operators *)
  | OOSlash | OOPercent
  | OOCaret | OOAmp | OOPipe | OOEqual (* = *)
  | OOLessLess | OOGreaterGreater
  | OOPlusEqual | OOMinusEqual | OOStarEqual
  | OOSlashEqual | OOPercentEqual | OOCaretEqual | OOAmpEqual
  | OOPipeEqual  | OOLessLessEqual | OOGreaterGreaterEqual
  | OOEqualEqual | OOExclaimEqual
  | OOLess | OOGreater
  | OOLessEqual | OOGreaterEqual | OOSpaceship
  | OOComma
  | OOArrowStar | OOArrow
  | OOSubscript
  (* short-circuiting *)
  | OOAmpAmp | OOPipePipe
  (* n-ary *)
  | OONew (array : bool) | OODelete (array : bool) | OOCall
  | OOCoawait (* | Conditional *)
.
#[global] Instance: EqDecision OverloadableOperator := ltac:(solve_decision).

Variant UnOp : Set :=
| Uminus	(* - *)
| Uplus	(* + *)
| Unot	(* ! *)
| Ubnot	(* ~ *)
| Uunsupported (_ : PrimString.string).
#[global] Instance: EqDecision UnOp.
Proof. solve_decision. Defined.
#[global] Instance UnOp_countable : Countable UnOp.
Proof.
  apply (inj_countable' (fun op =>
    match op with
    | Uminus => GenNode 0 []
    | Uplus => GenNode 1 []
    | Unot => GenNode 2 []
    | Ubnot => GenNode 3 []
    | Uunsupported op => GenNode 4 [GenLeaf op]
    end) (fun t =>
    match t with
    | GenNode 0 [] => Uminus
    | GenNode 1 [] => Uplus
    | GenNode 2 [] => Unot
    | GenNode 3 [] => Ubnot
    | GenNode 4 [GenLeaf op] => Uunsupported op
    | _ => Uminus	(* dummy *)
    end)).
  abstract (by intros []).
Defined.

Variant BinOp : Set :=
| Badd	(* + *)
| Band	(* & *)
| Bcmp	(* <=> *)
| Bdiv	(* / *)
| Beq	(* == *)
| Bge	(* >= *)
| Bgt	(* > *)
| Ble	(* <= *)
| Blt	(* < *)
| Bmul	(* * *)
| Bneq	(* != *)
| Bor	(* | *)
| Bmod	(* % *)
| Bshl	(* << *)
| Bshr	(* >> *)
| Bsub	(* - *)
| Bxor	(* ^ *)
| Bdotp	(* .* *)
| Bdotip	(* ->* *)
| Bunsupported (_ : PrimString.string).
#[global] Instance: EqDecision BinOp.
Proof. solve_decision. Defined.
#[global] Instance BinOp_countable : Countable BinOp.
Proof.
  apply (inj_countable' (fun op =>
    match op with
    | Badd => GenNode 0 []
    | Band => GenNode 1 []
    | Bcmp => GenNode 2 []
    | Bdiv => GenNode 3 []
    | Beq => GenNode 4 []
    | Bge => GenNode 5 []
    | Bgt => GenNode 6 []
    | Ble => GenNode 7 []
    | Blt => GenNode 8 []
    | Bmul => GenNode 9 []
    | Bneq => GenNode 10 []
    | Bor => GenNode 11 []
    | Bmod => GenNode 12 []
    | Bshl => GenNode 13 []
    | Bshr => GenNode 14 []
    | Bsub => GenNode 15 []
    | Bxor => GenNode 16 []
    | Bdotp => GenNode 17 []
    | Bdotip => GenNode 18 []
    | Bunsupported op => GenNode 19 [GenLeaf op]
    end) (fun t =>
    match t with
    | GenNode 0 [] => Badd
    | GenNode 1 [] => Band
    | GenNode 2 [] => Bcmp
    | GenNode 3 [] => Bdiv
    | GenNode 4 [] => Beq
    | GenNode 5 [] => Bge
    | GenNode 6 [] => Bgt
    | GenNode 7 [] => Ble
    | GenNode 8 [] => Blt
    | GenNode 9 [] => Bmul
    | GenNode 10 [] => Bneq
    | GenNode 11 [] => Bor
    | GenNode 12 [] => Bmod
    | GenNode 13 [] => Bshl
    | GenNode 14 [] => Bshr
    | GenNode 15 [] => Bsub
    | GenNode 16 [] => Bxor
    | GenNode 17 [] => Bdotp
    | GenNode 18 [] => Bdotip
    | GenNode 19 [GenLeaf op] => Bunsupported op
    | _ => Badd	(* dummy *)
    end)).
  abstract (by intros []).
Defined.


(** ** Evaluation Order *)
Module evaluation_order.
  Variant t : Set :=
  | nd (* fully non-deterministic *)
  | l_nd (* left then non-deterministic, calls.
            We use this for left-to-right *binary* operators *)
  | rl (* right-to-left, assignment operators (post C++17) *).

  (* The order of evaluation for each operator *when overloaded* *)
  Definition order_of (oo : OverloadableOperator) : t :=
    match oo with
    | OOTilde | OOExclaim => nd
    | OOPlusPlus | OOMinusMinus =>
      (* The evaluation order only matters for operator calls. For those, these
         are unary operators with a possible [Eint 0] as a second argument (to
         distinguish post-fix). The implicit argument is *always* a constant
         integer, so nothing is needed *)
      l_nd
    | OOStar => nd (* multiplication or deref *)
    | OOArrow => nd (* deref *)

    (* binary operators *)
    | OOPlus | OOMinus | OOSlash | OOPercent
    | OOCaret | OOAmp | OOPipe => nd

    (* shift operators are sequenced left-to-right: https://eel.is/c++draft/expr.shift#4. *)
    | OOLessLess | OOGreaterGreater => l_nd
    (* Assignment operators -- ordered right-to-left*)
    | OOEqual
    | OOPlusEqual  | OOMinusEqual | OOStarEqual
    | OOSlashEqual | OOPercentEqual | OOCaretEqual | OOAmpEqual
    | OOPipeEqual  | OOLessLessEqual | OOGreaterGreaterEqual => rl
    (* Comparison operators -- non-deterministic *)
    | OOEqualEqual | OOExclaimEqual
    | OOLess | OOGreater
    | OOLessEqual | OOGreaterEqual
    | OOSpaceship => nd

    | OOComma => l_nd (* http://eel.is/c++draft/expr.compound#expr.comma-1 *)
    | OOArrowStar => l_nd  (* left-to-right: http://eel.is/c++draft/expr.mptr.oper#4*)

    | OOSubscript => l_nd
    (* ^^ for primitives, the order is determined by the types, but when overloading
       the "object" is always on the left. http://eel.is/c++draft/expr.sub#1 *)

    (* Short circuiting *)
    | OOAmpAmp | OOPipePipe => l_nd
    (* ^^ for primitives, the evaluation is based on short-circuiting, but when
       overloading it is left-to-right. <http://eel.is/c++draft/expr.log.and#1>
       and <http://eel.is/c++draft/expr.log.and#1> *)

    | OOCall => l_nd
    (* ^^ post-C++17, the evaluation order for calls is the function first and then the
       arguments, sequenced non-deterministically. This holds for <<f(x)>> as well as
       <<(f.*foo)(x)>> (where <<(f.*foo)>> is sequenced before the evaluation of <<x>> *)
    | OONew _ | OODelete _ | OOCoawait => nd
    end.
End evaluation_order.

(** ** Atomic Builtins *)
Module AtomicOp.
  Definition t : Set := PrimString.string.
  Definition compare : t -> t -> _ := PrimString.compare.
  #[global] Instance t_eqdec: EqDecision t :=
    eqdec_pstring.
End AtomicOp.
#[global] Notation AtomicOp := AtomicOp.t.
#[global] Bind Scope pstring_scope with AtomicOp.t.

(** ** Builtins *)
Module BuiltinFn.
  Definition t : Set := PrimString.string.
  Definition compare : t -> t -> _ := PrimString.compare.
  #[global] Instance t_eqdec: EqDecision t :=
    eqdec_pstring.
End BuiltinFn.
#[global] Notation BuiltinFn := BuiltinFn.t.
#[global] Bind Scope pstring_scope with BuiltinFn.t.

(** ** Dispatch type, i.e. <<virtual>> or <<static>> *)
Variant dispatch_type : Set := Virtual | Direct | Static.
#[global] Instance: EqDecision dispatch_type.
Proof. solve_decision. Defined.
#[deprecated(since="20230716",note="use [dispatch_type].")]
Notation call_type := dispatch_type (only parsing).

(** ** Value categories
    Base value categories as of C++11.
 *)
Variant ValCat : Set := Lvalue | Prvalue | Xvalue.
#[global] Instance: EqDecision ValCat.
Proof. solve_decision. Defined.
#[global] Instance ValCat_countable : Countable ValCat.
Proof.
  apply (inj_countable
    (fun vc => match vc with Lvalue => 1 | Prvalue => 2 | Xvalue => 3 end)
    (fun n =>
    match n with
    | 1 => Some Lvalue
    | 2 => Some Prvalue
    | 3 => Some Xvalue
    | _ => None
    end)
  )%positive.
  abstract (by intros []).
Defined.

(** ** The way an operator call is desugared *)
Module operator_impl.
  Import UPoly.

  Variant t {obj_name type : Set} : Set :=
    | Func (fn_name : obj_name) (fn_type : type)
    | MFunc (fn_name : obj_name) (_ : dispatch_type) (fn_type : type).
  #[global] Arguments t : clear implicits.

  #[global] Instance t_eq_dec : EqDecision2 t.
  Proof. solve_decision. Defined.

  Definition functype {name type} (i : t name type) : type :=
    match i with
    | Func _ t => t
    | MFunc _ _ t => t
    end.

  Definition existsb {name type : Set} (f : name -> bool) (g : type -> bool)
    (i : operator_impl.t name type) : bool :=
    match i with
    | Func fn ft
    | MFunc fn _ ft => f fn || g ft
    end.

  Definition fmap {name type name' type' : Set} (f : name -> name') (g : type -> type')
    (i : t name type) : t name' type' :=
    match i with
    | Func fn ft => Func (f fn) (g ft)
    | MFunc fn dt ft => MFunc (f fn) dt (g ft)
    end.
  #[global] Arguments fmap _ _ _ _ _ _ & _ : assert.

  #[universes(polymorphic)]
    Definition traverse@{u | } {F : Set -> Type@{u}} `{!FMap F, !MRet F, AP : !Ap F}
    {name type name' type' : Set} (f : name -> F name') (g : type -> F type')
    (i : t name type) : F (t name' type') :=
    match i with
    | Func fn ft => Func <$> f fn <*> g ft
    | MFunc fn dt ft => (fun fn ft => MFunc fn dt ft) <$> f fn <*> g ft
    end.
  #[global] Arguments traverse _ _ _ _ _ _ _ _ _ & _ _ : assert.
  #[global] Hint Opaque traverse : typeclass_instances.

End operator_impl.

Module new_form.
  Variant t : Set :=
  | Allocating (pass_align : bool)
  | NonAllocating.
  #[global] Instance: EqDecision t := ltac:(solve_decision).
End new_form.
#[global] Notation new_form := (new_form.t).

Definition MethodRef_ (obj_name functype Expr : Set) : Set :=
  (obj_name * dispatch_type * functype) + Expr.

Module MethodRef.
  Definition existsb {name functype Expr : Set}
      (f : name -> bool) (g : functype -> bool) (h : Expr -> bool)
      (a : MethodRef_ name functype Expr) : bool :=
    match a with
    | inl p => f p.1.1 || g p.2
    | inr e => h e
    end.

  Import UPoly.

  Definition fmap {name name' functype functype' Expr Expr' : Set}
    (f : name -> name') (g : functype -> functype')
    (h : Expr -> Expr')
    (m : MethodRef_ name functype Expr) : MethodRef_ name' functype' Expr' :=
    match m with
    | inl p => inl (f p.1.1, p.1.2, g p.2)
    | inr e => inr (h e)
    end.
  #[global] Arguments fmap _ _ _ _ _ _ _ _ _ & _ : assert.

  (* don't use the notation? *)
  #[universes(polymorphic)]
  Definition traverse@{u | } {F : Set -> Type@{u}} `{FM: FMap F, AP : !Ap@{Set u Set Set} F}
  {name name' functype functype' Expr Expr' : Set}
  (f : name -> F name') (g : functype -> F functype')
  (h : Expr -> F Expr')
  (m : MethodRef_ name functype Expr) : F (MethodRef_ name' functype' Expr') :=
    let _ : Ap F := AP in
    match m return F (MethodRef_ name' functype' Expr') with
    | inl p => ap (Ap:=AP) (UPoly.fmap (FMap:=FM) (fun on t => inl (on, p.1.2, t)) $ f p.1.1) $ g p.2
    | inr e => UPoly.fmap (FMap:=FM) inr $ h e
    end.
  #[global] Arguments traverse _ _ _ _ _ _ _ _ _ _ _ & _ _ : assert.
  #[global] Hint Opaque traverse : typeclass_instances.

End MethodRef.

Variant SwitchBranch : Set :=
  | Exact (_ : Z)
  | Range (_ _ : Z).
#[global] Instance: EqDecision SwitchBranch.
Proof. solve_decision. Defined.
