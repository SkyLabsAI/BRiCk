(*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import stdpp.strings.
From Stdlib Require Import ZArith.
From Flocq.IEEE754 Require Import Binary BinarySingleNaN Bits.
Require Export skylabs.prelude.pstring.
Require Import skylabs.lang.cpp.syntax.prelude.
Require Export skylabs.prelude.arith.types.


(* TODO: is this worth its own file? *)

#[local] Set Primitive Projections.
#[local] Notation EqDecision1 T := (∀ (A : Set), EqDecision A -> EqDecision (T A)) (only parsing).
#[local] Notation EqDecision2 T := (∀ (A : Set), EqDecision A -> EqDecision1 (T A)) (only parsing).
#[local] Notation EqDecision3 T := (∀ (A : Set), EqDecision A -> EqDecision2 (T A)) (only parsing).
#[local] Tactic Notation "solve_decision" := intros; solve_decision.


#[local] Open Scope N_scope.

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

End float_type.

#[global] Notation Ffloat16 := float_type.Ffloat16.
#[global] Notation Ffloat := float_type.Ffloat.
#[global] Notation Fdouble := float_type.Fdouble.
#[global] Notation Flongdouble := float_type.Flongdouble.
#[global] Notation Ffloat128 := float_type.Ffloat128.

(** Flocq-backed carriers and operations for BRiCk floating values.

    BRiCk now gives every [float_type.t] a concrete Flocq carrier.  The
    portable formats are IEEE binary16 [Ffloat16], binary32 [Ffloat], binary64
    [Fdouble], and binary128 [Ffloat128].  [Flongdouble] is modeled as a
    distinct binary128-valued C++ type; cpp2v must only emit this constructor
    for targets whose Clang [long double] APFloat semantics are IEEE quad.
    x87/IBM-double-double long double layouts need a separate target-dependent
    storage model and remain a frontend-gated case.

    Portable NaN policy: arithmetic and narrowing/widening conversions use
    nearest-even rounding and canonicalize NaN results to [fp_default_nan].  The
    raw-bit interface [fp_of_bits]/[fp_to_bits] is intentionally payload
    preserving, so memory/raw-byte reasoning can retain arbitrary NaN payloads
    even though arithmetic results are canonicalized.  We do not model dynamic
    floating-point environment state, traps, fast-math rewrites, or extended
    precision. *)
Definition fp_supported (_ : float_type.t) : bool := true.

Definition fp_fraction_bits (ft : float_type.t) : Z :=
  match ft with
  | Ffloat16 => 10
  | Ffloat => 23
  | Fdouble => 52
  | Flongdouble => 112
  | Ffloat128 => 112
  end.

Definition fp_exponent_bits (ft : float_type.t) : Z :=
  match ft with
  | Ffloat16 => 5
  | Ffloat => 8
  | Fdouble => 11
  | Flongdouble => 15
  | Ffloat128 => 15
  end.

Definition fp_precision (ft : float_type.t) : Z := fp_fraction_bits ft + 1.
Definition fp_emax (ft : float_type.t) : Z := 2 ^ (fp_exponent_bits ft - 1).

Lemma fp_precision_gt_0 ft : (0 < fp_precision ft)%Z.
Proof. destruct ft; vm_compute; reflexivity. Qed.

Lemma fp_precision_lt_emax ft : (fp_precision ft < fp_emax ft)%Z.
Proof. destruct ft; vm_compute; reflexivity. Qed.

Definition fp_bitsize (ft : float_type.t) : bitsize.t :=
  match ft with
  | Ffloat16 => bitsize.W16
  | Ffloat => bitsize.W32
  | Fdouble => bitsize.W64
  | Flongdouble | Ffloat128 => bitsize.W128
  end.

Definition fp_carrier (ft : float_type.t) : Set :=
  match ft with
  | Ffloat16 => Binary.binary_float (10 + 1) (2 ^ (5 - 1))
  | Ffloat => Binary.binary_float (23 + 1) (2 ^ (8 - 1))
  | Fdouble => Binary.binary_float (52 + 1) (2 ^ (11 - 1))
  | Flongdouble => Binary.binary_float (112 + 1) (2 ^ (15 - 1))
  | Ffloat128 => Binary.binary_float (112 + 1) (2 ^ (15 - 1))
  end.

Definition fp_of_bits (ft : float_type.t) : Z -> fp_carrier ft :=
  match ft return Z -> fp_carrier ft with
  | Ffloat16 => ltac:(change (Z -> Binary.binary_float (10 + 1) (2 ^ (5 - 1))); exact (binary_float_of_bits 10 5 eq_refl eq_refl eq_refl))
  | Ffloat => ltac:(change (Z -> Binary.binary_float (23 + 1) (2 ^ (8 - 1))); exact (binary_float_of_bits 23 8 eq_refl eq_refl eq_refl))
  | Fdouble => ltac:(change (Z -> Binary.binary_float (52 + 1) (2 ^ (11 - 1))); exact (binary_float_of_bits 52 11 eq_refl eq_refl eq_refl))
  | Flongdouble => ltac:(change (Z -> Binary.binary_float (112 + 1) (2 ^ (15 - 1))); exact (binary_float_of_bits 112 15 eq_refl eq_refl eq_refl))
  | Ffloat128 => ltac:(change (Z -> Binary.binary_float (112 + 1) (2 ^ (15 - 1))); exact (binary_float_of_bits 112 15 eq_refl eq_refl eq_refl))
  end.

Definition fp_to_bits (ft : float_type.t) : fp_carrier ft -> Z :=
  match ft return fp_carrier ft -> Z with
  | Ffloat16 => ltac:(change (Binary.binary_float (10 + 1) (2 ^ (5 - 1)) -> Z); exact (bits_of_binary_float 10 5))
  | Ffloat => ltac:(change (Binary.binary_float (23 + 1) (2 ^ (8 - 1)) -> Z); exact (bits_of_binary_float 23 8))
  | Fdouble => ltac:(change (Binary.binary_float (52 + 1) (2 ^ (11 - 1)) -> Z); exact (bits_of_binary_float 52 11))
  | Flongdouble => ltac:(change (Binary.binary_float (112 + 1) (2 ^ (15 - 1)) -> Z); exact (bits_of_binary_float 112 15))
  | Ffloat128 => ltac:(change (Binary.binary_float (112 + 1) (2 ^ (15 - 1)) -> Z); exact (bits_of_binary_float 112 15))
  end.

Definition fp_compare_bits (ft : float_type.t) (x y : fp_carrier ft) : comparison :=
  Z.compare (fp_to_bits ft x) (fp_to_bits ft y).

Definition fp_default_nan_bits (ft : float_type.t) : Z :=
  match ft with
  | Ffloat16 => 32256%Z (* 0x7e00 *)
  | Ffloat => 2143289344%Z (* 0x7fc00000 *)
  | Fdouble => 9221120237041090560%Z (* 0x7ff8000000000000 *)
  | Flongdouble | Ffloat128 =>
      170138587312039964317873038467719495680%Z (* 0x7fff8000000000000000000000000000 *)
  end.

Definition fp_default_nan (ft : float_type.t) : fp_carrier ft :=
  fp_of_bits ft (fp_default_nan_bits ft).

Definition fp_zero (ft : float_type.t) : fp_carrier ft := fp_of_bits ft 0%Z.

Definition fp_is_nan (ft : float_type.t) : fp_carrier ft -> bool :=
  match ft return fp_carrier ft -> bool with
  | Ffloat16 => Binary.is_nan (10 + 1) (2 ^ (5 - 1))
  | Ffloat => Binary.is_nan (23 + 1) (2 ^ (8 - 1))
  | Fdouble => Binary.is_nan (52 + 1) (2 ^ (11 - 1))
  | Flongdouble => Binary.is_nan (112 + 1) (2 ^ (15 - 1))
  | Ffloat128 => Binary.is_nan (112 + 1) (2 ^ (15 - 1))
  end.

Definition fp_canonicalize_nan (ft : float_type.t) (f : fp_carrier ft) : fp_carrier ft :=
  if fp_is_nan ft f then fp_default_nan ft else f.

Definition fp_signed_zero (ft : float_type.t) (s : bool) : fp_carrier ft :=
  match ft return fp_carrier ft with
  | Ffloat16 => ltac:(change (Binary.binary_float (10 + 1) (2 ^ (5 - 1))); exact (@Binary.B754_zero (10 + 1) (2 ^ (5 - 1)) s))
  | Ffloat => ltac:(change (Binary.binary_float (23 + 1) (2 ^ (8 - 1))); exact (@Binary.B754_zero (23 + 1) (2 ^ (8 - 1)) s))
  | Fdouble => ltac:(change (Binary.binary_float (52 + 1) (2 ^ (11 - 1))); exact (@Binary.B754_zero (52 + 1) (2 ^ (11 - 1)) s))
  | Flongdouble => ltac:(change (Binary.binary_float (112 + 1) (2 ^ (15 - 1))); exact (@Binary.B754_zero (112 + 1) (2 ^ (15 - 1)) s))
  | Ffloat128 => ltac:(change (Binary.binary_float (112 + 1) (2 ^ (15 - 1))); exact (@Binary.B754_zero (112 + 1) (2 ^ (15 - 1)) s))
  end.

Definition fp_infinity (ft : float_type.t) (s : bool) : fp_carrier ft :=
  match ft return fp_carrier ft with
  | Ffloat16 => ltac:(change (Binary.binary_float (10 + 1) (2 ^ (5 - 1))); exact (@Binary.B754_infinity (10 + 1) (2 ^ (5 - 1)) s))
  | Ffloat => ltac:(change (Binary.binary_float (23 + 1) (2 ^ (8 - 1))); exact (@Binary.B754_infinity (23 + 1) (2 ^ (8 - 1)) s))
  | Fdouble => ltac:(change (Binary.binary_float (52 + 1) (2 ^ (11 - 1))); exact (@Binary.B754_infinity (52 + 1) (2 ^ (11 - 1)) s))
  | Flongdouble => ltac:(change (Binary.binary_float (112 + 1) (2 ^ (15 - 1))); exact (@Binary.B754_infinity (112 + 1) (2 ^ (15 - 1)) s))
  | Ffloat128 => ltac:(change (Binary.binary_float (112 + 1) (2 ^ (15 - 1))); exact (@Binary.B754_infinity (112 + 1) (2 ^ (15 - 1)) s))
  end.

Definition fp_unop_nan (ft : float_type.t) :
    fp_carrier ft -> { nan : fp_carrier ft | fp_is_nan ft nan = true } :=
  match ft return fp_carrier ft -> { nan : fp_carrier ft | fp_is_nan ft nan = true } with
  | Ffloat16 => fun _ => ltac:(change ({ nan : Binary.binary_float (10 + 1) (2 ^ (5 - 1)) | Binary.is_nan (10 + 1) (2 ^ (5 - 1)) nan = true }); exact (exist _ (@Binary.B754_nan (10 + 1) (2 ^ (5 - 1)) false xH eq_refl) eq_refl))
  | Ffloat => fun _ => ltac:(change ({ nan : Binary.binary_float (23 + 1) (2 ^ (8 - 1)) | Binary.is_nan (23 + 1) (2 ^ (8 - 1)) nan = true }); exact (exist _ (@Binary.B754_nan (23 + 1) (2 ^ (8 - 1)) false xH eq_refl) eq_refl))
  | Fdouble => fun _ => ltac:(change ({ nan : Binary.binary_float (52 + 1) (2 ^ (11 - 1)) | Binary.is_nan (52 + 1) (2 ^ (11 - 1)) nan = true }); exact (exist _ (@Binary.B754_nan (52 + 1) (2 ^ (11 - 1)) false xH eq_refl) eq_refl))
  | Flongdouble => fun _ => ltac:(change ({ nan : Binary.binary_float (112 + 1) (2 ^ (15 - 1)) | Binary.is_nan (112 + 1) (2 ^ (15 - 1)) nan = true }); exact (exist _ (@Binary.B754_nan (112 + 1) (2 ^ (15 - 1)) false xH eq_refl) eq_refl))
  | Ffloat128 => fun _ => ltac:(change ({ nan : Binary.binary_float (112 + 1) (2 ^ (15 - 1)) | Binary.is_nan (112 + 1) (2 ^ (15 - 1)) nan = true }); exact (exist _ (@Binary.B754_nan (112 + 1) (2 ^ (15 - 1)) false xH eq_refl) eq_refl))
  end.

Definition fp_binop_nan (ft : float_type.t) :
    fp_carrier ft -> fp_carrier ft -> { nan : fp_carrier ft | fp_is_nan ft nan = true } :=
  fun _ _ => fp_unop_nan ft (fp_zero ft).

Definition fp_neg (ft : float_type.t) : fp_carrier ft -> fp_carrier ft :=
  match ft return fp_carrier ft -> fp_carrier ft with
  | Ffloat16 => fun f => fp_canonicalize_nan Ffloat16 (Binary.Bopp _ _ (fp_unop_nan Ffloat16) f)
  | Ffloat => fun f => fp_canonicalize_nan Ffloat (Binary.Bopp _ _ (fp_unop_nan Ffloat) f)
  | Fdouble => fun f => fp_canonicalize_nan Fdouble (Binary.Bopp _ _ (fp_unop_nan Fdouble) f)
  | Flongdouble => fun f => fp_canonicalize_nan Flongdouble (Binary.Bopp _ _ (fp_unop_nan Flongdouble) f)
  | Ffloat128 => fun f => fp_canonicalize_nan Ffloat128 (Binary.Bopp _ _ (fp_unop_nan Ffloat128) f)
  end.

Definition fp_normalize_with_mode
    (m : BinarySingleNaN.mode) (ft : float_type.t) (z e : Z) (signed_zero : bool)
    : fp_carrier ft :=
  match ft return fp_carrier ft with
  | Ffloat16 => ltac:(change (Binary.binary_float (10 + 1) (2 ^ (5 - 1))); exact (Binary.binary_normalize (10 + 1) (2 ^ (5 - 1)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) m z e signed_zero))
  | Ffloat => ltac:(change (Binary.binary_float (23 + 1) (2 ^ (8 - 1))); exact (Binary.binary_normalize (23 + 1) (2 ^ (8 - 1)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) m z e signed_zero))
  | Fdouble => ltac:(change (Binary.binary_float (52 + 1) (2 ^ (11 - 1))); exact (Binary.binary_normalize (52 + 1) (2 ^ (11 - 1)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) m z e signed_zero))
  | Flongdouble => ltac:(change (Binary.binary_float (112 + 1) (2 ^ (15 - 1))); exact (Binary.binary_normalize (112 + 1) (2 ^ (15 - 1)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) m z e signed_zero))
  | Ffloat128 => ltac:(change (Binary.binary_float (112 + 1) (2 ^ (15 - 1))); exact (Binary.binary_normalize (112 + 1) (2 ^ (15 - 1)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) m z e signed_zero))
  end.

Definition fp_of_Z (ft : float_type.t) (z : Z) : fp_carrier ft :=
  fp_normalize_with_mode mode_NE ft z 0 false.

Definition fp_cast_with_mode
    (m : BinarySingleNaN.mode) (from to : float_type.t)
    : fp_carrier from -> fp_carrier to :=
  match from return fp_carrier from -> fp_carrier to with
  | Ffloat16 => fun f =>
      match f with
      | Binary.B754_zero _ _ s => fp_signed_zero to s
      | Binary.B754_infinity _ _ s => fp_infinity to s
      | Binary.B754_nan _ _ _ _ _ => fp_default_nan to
      | Binary.B754_finite _ _ s m' e _ => fp_normalize_with_mode m to (if s then Z.opp (Z.pos m') else Z.pos m') e s
      end
  | Ffloat => fun f =>
      match f with
      | Binary.B754_zero _ _ s => fp_signed_zero to s
      | Binary.B754_infinity _ _ s => fp_infinity to s
      | Binary.B754_nan _ _ _ _ _ => fp_default_nan to
      | Binary.B754_finite _ _ s m' e _ => fp_normalize_with_mode m to (if s then Z.opp (Z.pos m') else Z.pos m') e s
      end
  | Fdouble => fun f =>
      match f with
      | Binary.B754_zero _ _ s => fp_signed_zero to s
      | Binary.B754_infinity _ _ s => fp_infinity to s
      | Binary.B754_nan _ _ _ _ _ => fp_default_nan to
      | Binary.B754_finite _ _ s m' e _ => fp_normalize_with_mode m to (if s then Z.opp (Z.pos m') else Z.pos m') e s
      end
  | Flongdouble => fun f =>
      match f with
      | Binary.B754_zero _ _ s => fp_signed_zero to s
      | Binary.B754_infinity _ _ s => fp_infinity to s
      | Binary.B754_nan _ _ _ _ _ => fp_default_nan to
      | Binary.B754_finite _ _ s m' e _ => fp_normalize_with_mode m to (if s then Z.opp (Z.pos m') else Z.pos m') e s
      end
  | Ffloat128 => fun f =>
      match f with
      | Binary.B754_zero _ _ s => fp_signed_zero to s
      | Binary.B754_infinity _ _ s => fp_infinity to s
      | Binary.B754_nan _ _ _ _ _ => fp_default_nan to
      | Binary.B754_finite _ _ s m' e _ => fp_normalize_with_mode m to (if s then Z.opp (Z.pos m') else Z.pos m') e s
      end
  end.

(* [fp_cast ft ft] is not the semantic path for C++ identity casts.  C++
   identity conversions use [ConvFloatId]; this generic helper is for
   non-identity float-to-float conversion and may canonicalize NaNs. *)
Definition fp_cast (from to : float_type.t) : fp_carrier from -> fp_carrier to :=
  fp_cast_with_mode mode_NE from to.

Definition fp_float_to_double (f : fp_carrier Ffloat) : fp_carrier Fdouble :=
  fp_cast Ffloat Fdouble f.

Definition fp_double_to_float (f : fp_carrier Fdouble) : fp_carrier Ffloat :=
  fp_cast Fdouble Ffloat f.

Definition fp_add_with_mode (m : BinarySingleNaN.mode) (ft : float_type.t)
    : fp_carrier ft -> fp_carrier ft -> fp_carrier ft :=
  match ft return fp_carrier ft -> fp_carrier ft -> fp_carrier ft with
  | Ffloat16 => fun x y => fp_canonicalize_nan Ffloat16 (Binary.Bplus (10 + 1) (2 ^ (5 - 1)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (fp_binop_nan Ffloat16) m x y)
  | Ffloat => fun x y => fp_canonicalize_nan Ffloat (Binary.Bplus (23 + 1) (2 ^ (8 - 1)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (fp_binop_nan Ffloat) m x y)
  | Fdouble => fun x y => fp_canonicalize_nan Fdouble (Binary.Bplus (52 + 1) (2 ^ (11 - 1)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (fp_binop_nan Fdouble) m x y)
  | Flongdouble => fun x y => fp_canonicalize_nan Flongdouble (Binary.Bplus (112 + 1) (2 ^ (15 - 1)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (fp_binop_nan Flongdouble) m x y)
  | Ffloat128 => fun x y => fp_canonicalize_nan Ffloat128 (Binary.Bplus (112 + 1) (2 ^ (15 - 1)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (fp_binop_nan Ffloat128) m x y)
  end.

Definition fp_sub_with_mode (m : BinarySingleNaN.mode) (ft : float_type.t)
    : fp_carrier ft -> fp_carrier ft -> fp_carrier ft :=
  match ft return fp_carrier ft -> fp_carrier ft -> fp_carrier ft with
  | Ffloat16 => fun x y => fp_canonicalize_nan Ffloat16 (Binary.Bminus (10 + 1) (2 ^ (5 - 1)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (fp_binop_nan Ffloat16) m x y)
  | Ffloat => fun x y => fp_canonicalize_nan Ffloat (Binary.Bminus (23 + 1) (2 ^ (8 - 1)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (fp_binop_nan Ffloat) m x y)
  | Fdouble => fun x y => fp_canonicalize_nan Fdouble (Binary.Bminus (52 + 1) (2 ^ (11 - 1)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (fp_binop_nan Fdouble) m x y)
  | Flongdouble => fun x y => fp_canonicalize_nan Flongdouble (Binary.Bminus (112 + 1) (2 ^ (15 - 1)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (fp_binop_nan Flongdouble) m x y)
  | Ffloat128 => fun x y => fp_canonicalize_nan Ffloat128 (Binary.Bminus (112 + 1) (2 ^ (15 - 1)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (fp_binop_nan Ffloat128) m x y)
  end.

Definition fp_mul_with_mode (m : BinarySingleNaN.mode) (ft : float_type.t)
    : fp_carrier ft -> fp_carrier ft -> fp_carrier ft :=
  match ft return fp_carrier ft -> fp_carrier ft -> fp_carrier ft with
  | Ffloat16 => fun x y => fp_canonicalize_nan Ffloat16 (Binary.Bmult (10 + 1) (2 ^ (5 - 1)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (fp_binop_nan Ffloat16) m x y)
  | Ffloat => fun x y => fp_canonicalize_nan Ffloat (Binary.Bmult (23 + 1) (2 ^ (8 - 1)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (fp_binop_nan Ffloat) m x y)
  | Fdouble => fun x y => fp_canonicalize_nan Fdouble (Binary.Bmult (52 + 1) (2 ^ (11 - 1)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (fp_binop_nan Fdouble) m x y)
  | Flongdouble => fun x y => fp_canonicalize_nan Flongdouble (Binary.Bmult (112 + 1) (2 ^ (15 - 1)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (fp_binop_nan Flongdouble) m x y)
  | Ffloat128 => fun x y => fp_canonicalize_nan Ffloat128 (Binary.Bmult (112 + 1) (2 ^ (15 - 1)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (fp_binop_nan Ffloat128) m x y)
  end.

Definition fp_div_with_mode (m : BinarySingleNaN.mode) (ft : float_type.t)
    : fp_carrier ft -> fp_carrier ft -> fp_carrier ft :=
  match ft return fp_carrier ft -> fp_carrier ft -> fp_carrier ft with
  | Ffloat16 => fun x y => fp_canonicalize_nan Ffloat16 (Binary.Bdiv (10 + 1) (2 ^ (5 - 1)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (fp_binop_nan Ffloat16) m x y)
  | Ffloat => fun x y => fp_canonicalize_nan Ffloat (Binary.Bdiv (23 + 1) (2 ^ (8 - 1)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (fp_binop_nan Ffloat) m x y)
  | Fdouble => fun x y => fp_canonicalize_nan Fdouble (Binary.Bdiv (52 + 1) (2 ^ (11 - 1)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (fp_binop_nan Fdouble) m x y)
  | Flongdouble => fun x y => fp_canonicalize_nan Flongdouble (Binary.Bdiv (112 + 1) (2 ^ (15 - 1)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (fp_binop_nan Flongdouble) m x y)
  | Ffloat128 => fun x y => fp_canonicalize_nan Ffloat128 (Binary.Bdiv (112 + 1) (2 ^ (15 - 1)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (fp_binop_nan Ffloat128) m x y)
  end.

Definition fp_add := fp_add_with_mode mode_NE.
Definition fp_sub := fp_sub_with_mode mode_NE.
Definition fp_mul := fp_mul_with_mode mode_NE.
Definition fp_div := fp_div_with_mode mode_NE.

Definition fp_to_Z (ft : float_type.t) : fp_carrier ft -> option Z :=
  match ft return fp_carrier ft -> option Z with
  | Ffloat16 => fun f => if Binary.is_finite _ _ f then Some (Binary.Btrunc _ _ f) else None
  | Ffloat => fun f => if Binary.is_finite _ _ f then Some (Binary.Btrunc _ _ f) else None
  | Fdouble => fun f => if Binary.is_finite _ _ f then Some (Binary.Btrunc _ _ f) else None
  | Flongdouble => fun f => if Binary.is_finite _ _ f then Some (Binary.Btrunc _ _ f) else None
  | Ffloat128 => fun f => if Binary.is_finite _ _ f then Some (Binary.Btrunc _ _ f) else None
  end.

Definition fp_compare (ft : float_type.t) : fp_carrier ft -> fp_carrier ft -> option comparison :=
  match ft return fp_carrier ft -> fp_carrier ft -> option comparison with
  | Ffloat16 => Binary.Bcompare _ _
  | Ffloat => Binary.Bcompare _ _
  | Fdouble => Binary.Bcompare _ _
  | Flongdouble => Binary.Bcompare _ _
  | Ffloat128 => Binary.Bcompare _ _
  end.

Definition fp_is_true (ft : float_type.t) (f : fp_carrier ft) : bool :=
  match fp_compare ft f (fp_zero ft) with
  | Some Eq => false
  | _ => true
  end.

Lemma fp_compare_zero_zero_supported : forall ft,
  fp_supported ft = true -> fp_compare ft (fp_zero ft) (fp_zero ft) = Some Eq.
Proof.
  destruct ft; simpl; vm_compute; reflexivity.
Qed.

Lemma fp_is_true_zero_supported ft :
  fp_supported ft = true -> fp_is_true ft (fp_zero ft) = false.
Proof. intros Hft. rewrite /fp_is_true fp_compare_zero_zero_supported//. Qed.

Lemma fp_is_true_zero_Ffloat16 : fp_is_true Ffloat16 (fp_zero Ffloat16) = false.
Proof. apply fp_is_true_zero_supported. reflexivity. Qed.

Lemma fp_is_true_zero_Ffloat : fp_is_true Ffloat (fp_zero Ffloat) = false.
Proof. apply fp_is_true_zero_supported. reflexivity. Qed.

Lemma fp_is_true_zero_Fdouble : fp_is_true Fdouble (fp_zero Fdouble) = false.
Proof. apply fp_is_true_zero_supported. reflexivity. Qed.

Lemma fp_is_true_zero_Flongdouble : fp_is_true Flongdouble (fp_zero Flongdouble) = false.
Proof. apply fp_is_true_zero_supported. reflexivity. Qed.

Lemma fp_is_true_zero_Ffloat128 : fp_is_true Ffloat128 (fp_zero Ffloat128) = false.
Proof. apply fp_is_true_zero_supported. reflexivity. Qed.

Lemma fp_compare_zero_zero_Ffloat16 : fp_compare Ffloat16 (fp_zero Ffloat16) (fp_zero Ffloat16) = Some Eq.
Proof. apply fp_compare_zero_zero_supported. reflexivity. Qed.

Lemma fp_compare_zero_zero_Ffloat : fp_compare Ffloat (fp_zero Ffloat) (fp_zero Ffloat) = Some Eq.
Proof. apply fp_compare_zero_zero_supported. reflexivity. Qed.

Lemma fp_compare_zero_zero_Fdouble : fp_compare Fdouble (fp_zero Fdouble) (fp_zero Fdouble) = Some Eq.
Proof. apply fp_compare_zero_zero_supported. reflexivity. Qed.

Lemma fp_compare_zero_zero_Flongdouble : fp_compare Flongdouble (fp_zero Flongdouble) (fp_zero Flongdouble) = Some Eq.
Proof. apply fp_compare_zero_zero_supported. reflexivity. Qed.

Lemma fp_compare_zero_zero_Ffloat128 : fp_compare Ffloat128 (fp_zero Ffloat128) (fp_zero Ffloat128) = Some Eq.
Proof. apply fp_compare_zero_zero_supported. reflexivity. Qed.

Lemma fp_is_true_neg_zero_Ffloat16 : fp_is_true Ffloat16 (fp_of_bits Ffloat16 32768%Z) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma fp_is_true_neg_zero_Ffloat : fp_is_true Ffloat (fp_of_bits Ffloat 2147483648%Z) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma fp_is_true_neg_zero_Fdouble : fp_is_true Fdouble (fp_of_bits Fdouble 9223372036854775808%Z) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma fp_is_true_neg_zero_Flongdouble :
  fp_is_true Flongdouble (fp_of_bits Flongdouble 170141183460469231731687303715884105728%Z) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma fp_is_true_neg_zero_Ffloat128 :
  fp_is_true Ffloat128 (fp_of_bits Ffloat128 170141183460469231731687303715884105728%Z) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma fp_to_bits_default_nan_Ffloat16 :
  fp_to_bits Ffloat16 (fp_default_nan Ffloat16) = 32256%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma fp_to_bits_default_nan_Ffloat :
  fp_to_bits Ffloat (fp_default_nan Ffloat) = 2143289344%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma fp_to_bits_default_nan_Fdouble :
  fp_to_bits Fdouble (fp_default_nan Fdouble) = 9221120237041090560%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma fp_to_bits_default_nan_Flongdouble :
  fp_to_bits Flongdouble (fp_default_nan Flongdouble) =
  170138587312039964317873038467719495680%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma fp_to_bits_default_nan_Ffloat128 :
  fp_to_bits Ffloat128 (fp_default_nan Ffloat128) =
  170138587312039964317873038467719495680%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma fp_canonicalize_nan_result ft (f : fp_carrier ft) :
  fp_is_nan ft (fp_canonicalize_nan ft f) = true ->
  fp_canonicalize_nan ft f = fp_default_nan ft.
Proof.
  rewrite /fp_canonicalize_nan.
  destruct (fp_is_nan ft f) eqn:Hnan; first done.
  intros H; congruence.
Qed.

Lemma fp_neg_canonicalizes_nan ft (f : fp_carrier ft) :
  fp_is_nan ft (fp_neg ft f) = true -> fp_neg ft f = fp_default_nan ft.
Proof. destruct ft; cbn [fp_neg]; apply fp_canonicalize_nan_result. Qed.

Lemma fp_add_canonicalizes_nan ft (x y : fp_carrier ft) :
  fp_is_nan ft (fp_add ft x y) = true -> fp_add ft x y = fp_default_nan ft.
Proof. destruct ft; cbn [fp_add fp_add_with_mode]; apply fp_canonicalize_nan_result. Qed.

Lemma fp_sub_canonicalizes_nan ft (x y : fp_carrier ft) :
  fp_is_nan ft (fp_sub ft x y) = true -> fp_sub ft x y = fp_default_nan ft.
Proof. destruct ft; cbn [fp_sub fp_sub_with_mode]; apply fp_canonicalize_nan_result. Qed.

Lemma fp_mul_canonicalizes_nan ft (x y : fp_carrier ft) :
  fp_is_nan ft (fp_mul ft x y) = true -> fp_mul ft x y = fp_default_nan ft.
Proof. destruct ft; cbn [fp_mul fp_mul_with_mode]; apply fp_canonicalize_nan_result. Qed.

Lemma fp_div_canonicalizes_nan ft (x y : fp_carrier ft) :
  fp_is_nan ft (fp_div ft x y) = true -> fp_div ft x y = fp_default_nan ft.
Proof. destruct ft; cbn [fp_div fp_div_with_mode]; apply fp_canonicalize_nan_result. Qed.

Lemma fp_of_to_bits ft (f : fp_carrier ft) : fp_of_bits ft (fp_to_bits ft f) = f.
Proof.
  destruct ft; simpl in *.
  - exact (binary_float_of_bits_of_binary_float 10 5 (refl_equal _) (refl_equal _) (refl_equal _) f).
  - exact (binary_float_of_bits_of_binary_float 23 8 (refl_equal _) (refl_equal _) (refl_equal _) f).
  - exact (binary_float_of_bits_of_binary_float 52 11 (refl_equal _) (refl_equal _) (refl_equal _) f).
  - exact (binary_float_of_bits_of_binary_float 112 15 (refl_equal _) (refl_equal _) (refl_equal _) f).
  - exact (binary_float_of_bits_of_binary_float 112 15 (refl_equal _) (refl_equal _) (refl_equal _) f).
Qed.

Lemma fp_to_bits_range ft (f : fp_carrier ft) :
  (0 <= fp_to_bits ft f < 2 ^ bitsize.bitsZ (fp_bitsize ft))%Z.
Proof.
  destruct ft; simpl in *.
  - exact (bits_of_binary_float_range 10 5 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) f).
  - exact (bits_of_binary_float_range 23 8 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) f).
  - exact (bits_of_binary_float_range 52 11 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) f).
  - exact (bits_of_binary_float_range 112 15 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) f).
  - exact (bits_of_binary_float_range 112 15 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) f).
Qed.

Lemma fp_to_of_bits ft z :
  fp_supported ft = true ->
  (0 <= z < 2 ^ bitsize.bitsZ (fp_bitsize ft))%Z ->
  fp_to_bits ft (fp_of_bits ft z) = z.
Proof.
  destruct ft; simpl; intros _ Hz.
  - exact (bits_of_binary_float_of_bits 10 5 (refl_equal _) (refl_equal _) (refl_equal _) z Hz).
  - exact (bits_of_binary_float_of_bits 23 8 (refl_equal _) (refl_equal _) (refl_equal _) z Hz).
  - exact (bits_of_binary_float_of_bits 52 11 (refl_equal _) (refl_equal _) (refl_equal _) z Hz).
  - exact (bits_of_binary_float_of_bits 112 15 (refl_equal _) (refl_equal _) (refl_equal _) z Hz).
  - exact (bits_of_binary_float_of_bits 112 15 (refl_equal _) (refl_equal _) (refl_equal _) z Hz).
Qed.

Lemma fp_to_of_bits_Ffloat16 z :
  (0 <= z < 2 ^ 16)%Z -> fp_to_bits Ffloat16 (fp_of_bits Ffloat16 z) = z.
Proof. intros Hz. apply fp_to_of_bits; [reflexivity|exact Hz]. Qed.

Lemma fp_to_of_bits_Ffloat z :
  (0 <= z < 2 ^ 32)%Z -> fp_to_bits Ffloat (fp_of_bits Ffloat z) = z.
Proof. intros Hz. apply fp_to_of_bits; [reflexivity|exact Hz]. Qed.

Lemma fp_to_of_bits_Fdouble z :
  (0 <= z < 2 ^ 64)%Z -> fp_to_bits Fdouble (fp_of_bits Fdouble z) = z.
Proof. intros Hz. apply fp_to_of_bits; [reflexivity|exact Hz]. Qed.

Lemma fp_to_of_bits_Flongdouble z :
  (0 <= z < 2 ^ 128)%Z -> fp_to_bits Flongdouble (fp_of_bits Flongdouble z) = z.
Proof. intros Hz. apply fp_to_of_bits; [reflexivity|exact Hz]. Qed.

Lemma fp_to_of_bits_Ffloat128 z :
  (0 <= z < 2 ^ 128)%Z -> fp_to_bits Ffloat128 (fp_of_bits Ffloat128 z) = z.
Proof. intros Hz. apply fp_to_of_bits; [reflexivity|exact Hz]. Qed.

Lemma fp_of_to_bits_Ffloat16 (f : fp_carrier Ffloat16) :
  fp_of_bits Ffloat16 (fp_to_bits Ffloat16 f) = f.
Proof. apply fp_of_to_bits. Qed.

Lemma fp_of_to_bits_Ffloat (f : fp_carrier Ffloat) :
  fp_of_bits Ffloat (fp_to_bits Ffloat f) = f.
Proof. apply fp_of_to_bits. Qed.

Lemma fp_of_to_bits_Fdouble (f : fp_carrier Fdouble) :
  fp_of_bits Fdouble (fp_to_bits Fdouble f) = f.
Proof. apply fp_of_to_bits. Qed.

Lemma fp_of_to_bits_Flongdouble (f : fp_carrier Flongdouble) :
  fp_of_bits Flongdouble (fp_to_bits Flongdouble f) = f.
Proof. apply fp_of_to_bits. Qed.

Lemma fp_of_to_bits_Ffloat128 (f : fp_carrier Ffloat128) :
  fp_of_bits Ffloat128 (fp_to_bits Ffloat128 f) = f.
Proof. apply fp_of_to_bits. Qed.

Lemma fp_to_bits_inj ft : Inj (=) (=) (fp_to_bits ft).
Proof.
  intros x y Hbits.
  apply (f_equal (fp_of_bits ft)) in Hbits.
  by rewrite !fp_of_to_bits in Hbits.
Qed.

#[global] Instance fp_carrier_eq_dec ft : EqDecision (fp_carrier ft).
Proof.
  intros x y.
  destruct (Z.eq_dec (fp_to_bits ft x) (fp_to_bits ft y)) as [Hbits|Hbits].
  - left. by apply fp_to_bits_inj.
  - right. intros ->. by apply Hbits.
Defined.

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
