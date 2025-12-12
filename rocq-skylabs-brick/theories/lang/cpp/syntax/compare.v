(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.prelude.compare.
Require Import bluerock.prelude.pstring.
Require Import bluerock.lang.cpp.syntax.prelude.
Require Import bluerock.lang.cpp.syntax.preliminary.
Require Import bluerock.lang.cpp.syntax.overloadable.
Require Import bluerock.lang.cpp.syntax.literal_string.
Require Import bluerock.lang.cpp.syntax.core.
Require Stdlib.Numbers.Cyclic.Int63.PrimInt63.

#[local] Set Primitive Projections.
#[local] Open Scope positive_scope.

(* BEGIN: temporary infrastructure *)
  Structure comparator :=
    { _car : Set
    ; #[canonical=no] _compare :> _car -> _car -> comparison
    }.
  Arguments _compare {_} _ _.
  Canonical unit_comparator :=
    {| _car := unit
    ; _compare := fun _ _ => Eq |}.

  Canonical pair_comparator (C1 C2 : comparator) :=
    {| _car := C1.(_car) * C2.(_car)
    ; _compare := fun '(a,b) '(c,d) => compare_lex (C1.(_compare) a c) $ fun _ => C2.(_compare) b d |}.
  Canonical bs_comparator :=
    {| _car := bs
    ; _compare := bs_compare |}.
  Canonical pstring_comparator :=
    {| _car := PrimString.string
    ; _compare := PrimString.compare |}.
  Canonical localname_comparator :=
    {| _car := localname
     ; _compare := PrimString.compare |}.
  Canonical ident_comparator :=
    {| _car := ident
    ; _compare := PrimString.compare |}.
  Canonical bool_comparator :=
    {| _car := bool
    ; _compare := Bool.compare |}.
  Definition SwitchBranch_compare (a b : SwitchBranch) : comparison :=
    match a , b with
    | Exact a , Exact b => Z.compare a b
    | Exact _ , Range _ _ => Lt
    | Range _ _ , Exact _ => Gt
    | Range a b , Range c d => compare_lex (Z.compare a c) $ fun _ => Z.compare b d
    end.
  #[local] Canonical SwitchBranch_comparator :=
    {| _car := SwitchBranch
     ; _compare := SwitchBranch_compare |}.
(* END: temporary infrastructure *)

Instance unit_comparator_leibniz : LeibnizComparison unit_comparator.
Proof. red; by destruct a, b. Qed.

Definition by_tag_leibniz {T} (f : T -> positive) {Hinj : Inj eq eq f}
  : LeibnizComparison (fun a b => Pos.compare (f a) (f b)).
Proof. red; move=> ? ? /Pos.compare_eq; apply inj; apply _. Qed.

Instance byte_cmp_leibniz : LeibnizComparison byte_cmp.
Proof. red; rewrite /byte_cmp; move=> ? ? /N.compare_eq. apply inj. apply _. Qed.

Instance bs_cmp_leibniz : LeibnizComparison bs_cmp.
Proof.
  red.
  induction a; move=> [|y ys]; eauto; try inversion 1.
  generalize (LeibnizComparison.cmp_eq byte_cmp b y).
  case_match; try inversion H1.
  intros; f_equal; eauto.
Qed.

Module cast_style.
  #[prefix="",only(tag)] derive cast_style.t.
  Definition compare (a b : cast_style.t) : comparison :=
    Pos.compare (tag a) (tag b).
End cast_style.

Canonical cast_style_comparator :=
  {| _car := cast_style.t
  ; _compare := cast_style.compare |}.


Module sum.
  Section compare.
    Context {A B : Type}.
    Context (compareA : A -> A -> comparison).
    Context (compareB : B -> B -> comparison).

    Definition compare (s s' : A + B) : comparison :=
      match s , s' with
      | inl a , inl a' => compareA a a'
      | inl _ , inr _ => Lt
      | inr _ , inl _ => Gt
      | inr b , inr b' => compareB b b'
      end.

  End compare.
End sum.
#[global] Instance sum_compare `{!Compare A, !Compare B} : Compare (A + B)%type := sum.compare compare compare.

Module prod.
  Section compare.
    Context {A B : Type}.
    Context (compareA : A -> A -> comparison).
    Context (compareB : B -> B -> comparison).

    Definition compare (p1 p2 : A * B) : comparison :=
      match p1, p2 with
      | (a1, b1) , (a2 , b2) => compare_lex (compareA a1 a2) $ fun _ => compareB b1 b2
      end.
  End compare.
End prod.
#[global] Instance prod_compare `{!Compare A, !Compare B} : Compare (A * B) := prod.compare compare compare.

Module option.
  Section compare.
    Context {A : Type}.
    Context (compareA : A -> A -> comparison).

    Definition compare (x y : option A) : comparison :=
      match x , y with
      | Some a , Some a' => compareA a a'
      | Some _ , None => Lt
      | None , Some _ => Gt
      | None , None => Eq
      end.

  End compare.
End option.
#[global] Instance option_compare `{!Compare A} : Compare (option A) := option.compare compare.

Module List.
  Section compare.
    Context {A : Type}.
    Context (compareA : A -> A -> comparison).

    (* for types with a small number of constructors the direct comparison function is faster *)
    Fixpoint compare (l l' : list A) : comparison :=
      match l , l' with
      | nil , nil => Eq
      | nil , _ :: _ => Lt
      | _ :: _ , nil => Gt
      | x :: xs , y :: ys => compare_lex (compareA x y) (fun _ => compare xs ys)
      end.

  End compare.
End List.
#[global] Instance list_compare `{!Compare A} : Compare (list A) := List.compare compare.

Canonical option_comparator (C1 : comparator) :=
  {| _car := option C1.(_car)
  ; _compare := option.compare C1.(_compare) |}.
Canonical list_comparator (C1 : comparator) :=
  {| _car := list C1.(_car)
  ; _compare := List.compare C1.(_compare) |}.

Module ValCat.
  #[prefix="", only(tag)] derive ValCat.

  Definition compare (x y : ValCat) : comparison :=
    Pos.compare (tag x) (tag y).
End ValCat.
#[global] Instance ValCat_compare : Compare ValCat := ValCat.compare.

Module UnOp.
  #[prefix="", only(tag)] derive UnOp.
  Definition car (t : positive) : Set :=
    match t with
    | 5 => PrimString.string
    | _ => unit
    end.
  Definition data (x : UnOp) : car (tag x) :=
    match x with
    | Uunsupported msg => msg
    | _ => ()
    end.
  Definition compare_data (t : positive) : car t -> car t -> comparison :=
    match t with
    | 5 => PrimString.compare
    | _ => fun _ _ => Eq
    end.

  #[local] Tactic Notation "compare_ctor" uconstr(x) :=
    let t := eval red in (tag x) in
    let d := eval red in (data x) in
    exact (compare_ctor tag car data compare_data t (fun _ => d)).
  #[local] Notation compare_ctor x := ltac:(compare_ctor x) (only parsing).
  #[local] Tactic Notation "compare_tag" uconstr(x) :=
    let t := eval red in (tag x) in
    exact (fun y => Pos.compare t (tag y)).
  #[local] Notation compare_tag x := ltac:(compare_tag x) (only parsing).

  Definition compare (op : UnOp) : UnOp -> comparison :=
    match op with
    | Uminus => compare_tag Uminus
    | Uplus => compare_tag Uplus
    | Unot => compare_tag Unot
    | Ubnot => compare_tag Ubnot
    | Uunsupported msg => compare_ctor (Uunsupported msg)
    end.

End UnOp.
#[global] Instance UnOp_compare : Compare UnOp := UnOp.compare.

Module BinOp.
  #[prefix="", only(tag)] derive BinOp.
  Definition car (t : positive) : Set :=
    match t with
    | 20 => PrimString.string
    | _ => unit
    end.
  Definition data (x : BinOp) : car (tag x) :=
    match x with
    | Bunsupported msg => msg
    | _ => ()
    end.
  Definition compare_data (t : positive) : car t -> car t -> comparison :=
    match t with
    | 20 => PrimString.compare
    | _ => fun _ _ => Eq
    end.

  #[local] Tactic Notation "compare_ctor" uconstr(x) :=
    let t := eval red in (tag x) in
    let d := eval red in (data x) in
    exact (compare_ctor tag car data compare_data t (fun _ => d)).
  #[local] Notation compare_ctor x := ltac:(compare_ctor x) (only parsing).
  #[local] Tactic Notation "compare_tag" uconstr(x) :=
    let t := eval red in (tag x) in
    exact (fun y => Pos.compare t (tag y)).
  #[local] Notation compare_tag x := ltac:(compare_tag x) (only parsing).

  Definition compare (op : BinOp) : BinOp -> comparison :=
    match op with
    | Badd => compare_tag Badd
    | Band => compare_tag Band
    | Bcmp => compare_tag Bcmp
    | Bdiv => compare_tag Bdiv
    | Beq => compare_tag Beq
    | Bge => compare_tag Bge
    | Bgt => compare_tag Bgt
    | Ble => compare_tag Ble
    | Blt => compare_tag Blt
    | Bmul => compare_tag Bmul
    | Bneq => compare_tag Bneq
    | Bor => compare_tag Bor
    | Bmod => compare_tag Bmod
    | Bshl => compare_tag Bshl
    | Bshr => compare_tag Bshr
    | Bsub => compare_tag Bsub
    | Bxor => compare_tag Bxor
    | Bdotp => compare_tag Bdotp
    | Bdotip => compare_tag Bdotip
    | Bunsupported msg => compare_ctor (Bunsupported msg)
    end.

End BinOp.
#[global] Instance BinOp_compare : Compare BinOp := BinOp.compare.

Module RUnOp.
  #[prefix="", only(tag)] derive RUnOp.
  Definition car (t : positive) : Set :=
    match t with
    | 1 => UnOp
    | _ => unit
    end.
  Definition data (x : RUnOp) : car (tag x) :=
    match x with
    | Runop op => op
    | _ => ()
    end.
  Definition compare_data (t : positive) : car t -> car t -> comparison :=
    match t with
    | 1 => UnOp.compare
    | _ => fun _ _ => Eq
    end.

  #[local] Tactic Notation "compare_ctor" uconstr(x) :=
    let t := eval red in (tag x) in
    let d := eval red in (data x) in
    exact (compare_ctor tag car data compare_data t (fun _ => d)).
  #[local] Notation compare_ctor x := ltac:(compare_ctor x) (only parsing).
  #[local] Tactic Notation "compare_tag" uconstr(x) :=
    let t := eval red in (tag x) in
    exact (fun y => Pos.compare t (tag y)).
  #[local] Notation compare_tag x := ltac:(compare_tag x) (only parsing).

  Definition compare (op : RUnOp) : RUnOp -> comparison :=
    match op with
    | Runop op => compare_ctor (Runop op)
    | Rpreinc => compare_tag Rpreinc
    | Rpredec => compare_tag Rpredec
    | Rpostinc => compare_tag Rpostinc
    | Rpostdec => compare_tag Rpostdec
    | Rstar => compare_tag Rstar
    | Rarrow => compare_tag Rarrow
    end.

End RUnOp.
#[global] Instance RUnOp_compare : Compare RUnOp := RUnOp.compare.

Module RBinOp.
  #[prefix="", only(tag)] derive RBinOp.
  Definition car (t : positive) : Set :=
    match t with
    | 1 | 3 => BinOp
    | _ => unit
    end.
  Definition data (x : RBinOp) : car (tag x) :=
    match x with
    | Rbinop op | Rassign_op op => op
    | _ => ()
    end.
  Definition compare_data (t : positive) : car t -> car t -> comparison :=
    match t with
    | 1 | 3 => BinOp.compare
    | _ => fun _ _ => Eq
    end.

  #[local] Tactic Notation "compare_ctor" uconstr(x) :=
    let t := eval red in (tag x) in
    let d := eval red in (data x) in
    exact (compare_ctor tag car data compare_data t (fun _ => d)).
  #[local] Notation compare_ctor x := ltac:(compare_ctor x) (only parsing).
  #[local] Tactic Notation "compare_tag" uconstr(x) :=
    let t := eval red in (tag x) in
    exact (fun y => Pos.compare t (tag y)).
  #[local] Notation compare_tag x := ltac:(compare_tag x) (only parsing).

  Definition compare (op : RBinOp) : RBinOp -> comparison :=
    match op with
    | Rbinop op => compare_ctor (Rbinop op)
    | Rassign => compare_tag Rassign
    | Rassign_op op => compare_ctor (Rassign_op op)
    | Rsubscript => compare_tag Rsubscript
    end.

End RBinOp.
#[global] Instance RBinOp_compare : Compare RBinOp := RBinOp.compare.

Module bitsize.
  #[prefix="", only(tag)] derive bitsize.

  Definition compare (x y : bitsize) : comparison :=
    Pos.compare (tag x) (tag y).
End bitsize.
#[global] Instance bitsize_compare : Compare bitsize := bitsize.compare.

Module int_rank.
  #[prefix="", only(tag)] derive int_rank.t.
  Import PrimInt63.

  Definition prim_tag (r : int_rank.t) : PrimInt63.int :=
    match r with
    | int_rank.Ichar => 1
    | int_rank.Ishort => 2
    | int_rank.Iint => 3
    | int_rank.Ilong => 4
    | int_rank.Ilonglong => 5
    | int_rank.I128 => 6
    end%uint63.

  Definition compare (x y : int_rank.t) : comparison :=
    PrimInt63.compare (prim_tag x) (prim_tag y).
End int_rank.
#[global] Instance int_rank_compare : Compare int_rank := int_rank.compare.

Module signed.
  Definition compare (x y : signed) : comparison :=
    match x , y with
    | Signed , Signed => Eq
    | Signed , Unsigned => Lt
    | Unsigned , Signed => Gt
    | Unsigned , Unsigned => Eq
    end.
End signed.
#[global] Instance signed_compare : Compare signed := signed.compare.

Module char_type.
  #[prefix="", only(tag)] derive char_type.t.
  Import PrimInt63.

  Definition prim_tag (r : char_type.t) : PrimInt63.int :=
    match r with
    | char_type.Cchar => 1
    | char_type.Cwchar => 2
    | char_type.C8 => 3
    | char_type.C16 => 4
    | char_type.C32 => 5
    end%uint63.

  Definition compare (x y : char_type.t) : comparison :=
    PrimInt63.compare (prim_tag x) (prim_tag y).
End char_type.
#[global] Instance char_type_compare : Compare char_type.t := char_type.compare.

Module float_type.
  #[prefix="", only(tag)] derive float_type.t.

  Definition compare (x y : float_type.t) : comparison :=
    Pos.compare (tag x) (tag y).
End float_type.
#[global] Instance float_type_compare : Compare float_type.t := float_type.compare.

Module type_qualifiers.
  #[prefix="", only(tag)] derive type_qualifiers.
  Import PrimInt63.

  Definition prim_tag (t : type_qualifiers) : PrimInt63.int :=
    match t with
    | QCV => 0
    | QC => 1
    | QV => 2
    | QM => 3
    end%uint63.

  Definition compare (x y : type_qualifiers) : comparison :=
    PrimInt63.compare (prim_tag x) (prim_tag y).
End type_qualifiers.
#[global] Instance type_qualifiers_compare : Compare type_qualifiers := type_qualifiers.compare.

Definition compare_unit (a b : unit) : comparison := Eq.

Module dispatch_type.
  Definition compare (x y : dispatch_type) : comparison :=
    match x , y with
    | Virtual , Virtual => Eq
    | Virtual , Direct => Lt
    | Direct , Virtual => Gt
    | Direct , Direct => Eq
    end.
End dispatch_type.
#[global] Instance dispatch_type_compare : Compare dispatch_type := dispatch_type.compare.

Module MethodRef.
  Section compare.
    Context {obj_name functype Expr : Set}.
    Context (compareON : obj_name -> obj_name -> comparison).
    Context (compareFT : functype -> functype -> comparison).
    Context (compareE : Expr -> Expr -> comparison).
    #[local] Notation MethodRef := (MethodRef_ obj_name functype Expr).

    Definition compare : MethodRef -> MethodRef -> comparison :=
      sum.compare (
        fun '(n1, d1, t1) '(n2, d2, t2) =>
        compare_lex (compareON n1 n2) $ fun _ =>
        compare_lex (dispatch_type.compare d1 d2) $ fun _ =>
        compareFT t1 t2
      ) compareE.
  End compare.
End MethodRef.
#[global] Hint Opaque MethodRef_ : typeclass_instances.
#[global] Instance MethodRef_compare {A B C : Set} `{!Compare A, !Compare B, !Compare C} : Compare (MethodRef_ A B C) := MethodRef.compare compare compare compare.

Module operator_impl.
  Export preliminary.operator_impl.

  Section compare.
    Context {obj_name type : Set}.
    Context (compareON : obj_name -> obj_name -> comparison).
    Context (compareT : type -> type -> comparison).
    #[local] Notation t := (t obj_name type).

    Record box_Func : Set := Box_Func {
      box_Func_0 : obj_name;
      box_Func_1 : type;
    }.
    Definition box_Func_compare  (b1 b2 : box_Func) : comparison :=
      compare_lex (compareON b1.(box_Func_0) b2.(box_Func_0)) $ fun _ =>
      compareT b1.(box_Func_1) b2.(box_Func_1).

    Record box_MFunc : Set := Box_MFunc {
      box_MFunc_0 : obj_name;
      box_MFunc_1 : dispatch_type;
      box_MFunc_2 : type;
    }.
    Definition box_MFunc_compare (b1 b2 : box_MFunc) : comparison :=
      compare_lex (compareON b1.(box_MFunc_0) b2.(box_MFunc_0)) $ fun _ =>
      compare_lex (dispatch_type.compare b1.(box_MFunc_1) b2.(box_MFunc_1)) $ fun _ =>
      compareT b1.(box_MFunc_2) b2.(box_MFunc_2).

    Definition tag (p : t) : positive :=
      match p with
      | Func _ _ => 1
      | MFunc _ _ _ => 2
      end.
    Definition car (t : positive) : Set :=
      match t with
      | 1 => box_Func
      | _ => box_MFunc
      end.
    Definition data (p : t) : car (tag p) :=
      match p with
      | Func on t => Box_Func on t
      | MFunc on d t => Box_MFunc on d t
      end.
    Definition compare_data (t : positive) : car t -> car t -> comparison :=
      match t with
      | 1 => box_Func_compare
      | _ => box_MFunc_compare
      end.

    #[local] Notation compare_ctor := (compare_ctor tag car data compare_data).

    Definition compare (p : t) : t -> comparison :=
      match p with
      | Func on t => compare_ctor (Reduce (tag (Func on t))) (fun _ => Reduce (data (Func on t)))
      | MFunc on d t => compare_ctor (Reduce (tag (MFunc on d t))) (fun _ => Reduce (data (MFunc on d t)))
      end.
  End compare.

End operator_impl.
#[global] Instance operator_impl_compare {A B : Set} `{!Compare A, !Compare B} : Compare (operator_impl.t A B) := operator_impl.compare compare compare.

#[global] Instance AtomicOp_compare : Compare AtomicOp := AtomicOp.compare.

Module calling_conv.
  #[prefix="", only(tag)] derive calling_conv.

  Definition compare (x y : calling_conv) : comparison :=
    Pos.compare (tag x) (tag y).
End calling_conv.
#[global] Instance calling_conv_compare : Compare calling_conv := calling_conv.compare.

Module function_arity.
  Definition compare (x y : function_arity) : comparison :=
    match x , y with
    | Ar_Definite , Ar_Definite => Eq
    | Ar_Definite , Ar_Variadic => Lt
    | Ar_Variadic , Ar_Definite => Gt
    | Ar_Variadic , Ar_Variadic => Eq
    end.
End function_arity.
#[global] Instance function_arity_compare : Compare function_arity := function_arity.compare.

Module new_form.
  Export preliminary.new_form.

  Definition compare (a b : new_form) : comparison :=
    match a , b with
    | Allocating b , Allocating b' => Bool.compare b b'
    | Allocating _ , NonAllocating => Lt
    | NonAllocating , Allocating _ => Gt
    | NonAllocating , NonAllocating => Eq
    end.

End new_form.
#[global] Instance new_form_compare : Compare new_form := new_form.compare.

Module function_type.

  Definition compare {type : Set} (compareT : type -> type -> comparison)
      (x y : function_type_ type) : comparison :=
    compare_lex (compareT x.(ft_return) y.(ft_return)) $ fun _ =>
    compare_lex (List.compare compareT x.(ft_params) y.(ft_params)) $ fun _ =>
    compare_lex (calling_conv.compare x.(ft_cc) y.(ft_cc)) $ fun _ =>
    function_arity.compare x.(ft_arity) y.(ft_arity).

End function_type.
#[global] Instance function_type_compare {A : Set} `{!Compare A} : Compare (function_type_ A) := function_type.compare compare.

Module temp_param.
  Section compare.
    Context {type : Set}.
    Context (compareT : type -> type -> comparison).
    #[local] Notation temp_param := (temp_param_ type).

    Record box_Pvalue : Set := Box_Pvalue {
      box_Pvalue_0 : ident;
      box_Pvalue_1 : type;
    }.
    Definition box_Pvalue_compare (b1 b2 : box_Pvalue) : comparison :=
      compare_lex (PrimString.compare b1.(box_Pvalue_0) b2.(box_Pvalue_0)) $ fun _ =>
      compareT b1.(box_Pvalue_1) b2.(box_Pvalue_1).

    Definition tag (p : temp_param) : positive :=
      match p with
      | Ptype _ => 1
      | Pvalue _ _ => 2
      | Punsupported _ => 3
      end.
    Definition car (t : positive) : Set :=
      match t with
      | 2 => box_Pvalue
      | _ => ident
      end.
    Definition data (p : temp_param) : car (tag p) :=
      match p with
      | Ptype id => id
      | Pvalue id t => Box_Pvalue id t
      | Punsupported msg => msg
      end.
    Definition compare_data (t : positive) : car t -> car t -> comparison :=
      match t with
      | 2 => box_Pvalue_compare
      | _ => PrimString.compare
      end.

    #[local] Notation compare_ctor := (compare_ctor tag car data compare_data).

    Definition compare (p : temp_param_ type) : temp_param_ type -> comparison :=
      match p with
      | Ptype id => compare_ctor (Reduce (tag (Ptype id))) (fun _ => Reduce (data (Ptype id)))
      | Pvalue id ty => compare_ctor (Reduce (tag (Pvalue id ty))) (fun _ => Reduce (data (Pvalue id ty)))
      | Punsupported msg => compare_ctor (Reduce (tag (Punsupported msg))) (fun _ => Reduce (data (Punsupported msg)))
      end.
  End compare.

End temp_param.
#[global] Instance temp_param_compare {A : Set} `{!Compare A} : Compare (temp_param_ A) := temp_param.compare compare.

Module temp_arg.
  Section compare.
    Context (compareN : name -> name -> comparison).
    Context (compareT : type -> type -> comparison).
    Context (compareE : Expr -> Expr -> comparison).

    Definition tag (p : temp_arg) : positive :=
      match p with
      | Atype _ => 1
      | Avalue _ => 2
      | Apack _ => 3
      | Atemplate _ => 4
      | Aunsupported _ => 5
      end.
    Definition car (t : positive) : Set :=
      match t with
      | 1 => type
      | 2 => Expr
      | 3 => list temp_arg
      | 4 => name
      | _ => PrimString.string
      end.
    Definition data (p : temp_arg) : car (tag p) :=
      match p with
      | Atype t => t
      | Avalue e => e
      | Apack ls => ls
      | Atemplate n => n
      | Aunsupported msg => msg
      end.
    Definition compare_data (ta_compare : temp_arg -> temp_arg -> comparison)
      (t : positive) : car t -> car t -> comparison :=
      match t with
      | 1 => compareT
      | 2 => compareE
      | 3 => List.compare ta_compare
      | 4 => compareN
      | _ => PrimString.compare
      end.

    #[local] Notation compare_ctor compare := (compare_ctor tag car data $ compare_data compare).

    Fixpoint compare (p : temp_arg) : temp_arg -> comparison :=
      match p with
      | Atype t => compare_ctor compare (Reduce (tag (Atype t))) (fun _ => Reduce (data (Atype t)))
      | Avalue e => compare_ctor compare (Reduce (tag (Avalue e))) (fun _ => Reduce (data (Avalue e)))
      | Apack ls => compare_ctor compare (Reduce (tag (Apack ls))) (fun _ => Reduce (data (Apack ls)))
      | Atemplate n => compare_ctor compare (Reduce (tag (Atemplate n))) (fun _ => Reduce (data (Atemplate n)))
      | Aunsupported msg => compare_ctor compare (Reduce (tag (Aunsupported msg))) (fun _ => Reduce (data (Aunsupported msg)))
      end.
  End compare.

End temp_arg.

Module OverloadableOperator.
  #[prefix="", only(tag)] derive OverloadableOperator.

  Section compare.
    #[local] Notation OO := OverloadableOperator.
    Import PrimInt63.

    Definition prim_tag (oo : OverloadableOperator) : PrimInt63.int :=
      match oo with
      | OOTilde => 1
      | OOExclaim => 2
      | OOPlusPlus => 3
      | OOMinusMinus => 4
      | OOStar => 5
      | OOPlus => 6
      | OOMinus => 7
      | OOSlash => 8
      | OOPercent => 9
      | OOCaret => 10
      | OOAmp => 11
      | OOPipe => 12
      | OOEqual => 13
      | OOLessLess => 14
      | OOGreaterGreater => 15
      | OOPlusEqual => 16
      | OOMinusEqual => 17
      | OOStarEqual => 18
      | OOSlashEqual => 19
      | OOPercentEqual => 20
      | OOCaretEqual => 21
      | OOAmpEqual => 22
      | OOPipeEqual => 23
      | OOLessLessEqual => 24
      | OOGreaterGreaterEqual => 25
      | OOEqualEqual => 26
      | OOExclaimEqual => 27
      | OOLess => 28
      | OOGreater => 29
      | OOLessEqual => 30
      | OOGreaterEqual => 31
      | OOSpaceship => 32
      | OOComma => 33
      | OOArrowStar => 34
      | OOArrow => 35
      | OOSubscript => 36
      | OOAmpAmp => 37
      | OOPipePipe => 38
      | OONew false => 39
      | OONew true => 40
      | OODelete false => 41
      | OODelete true => 42
      | OOCall => 43
      | OOCoawait => 44
    end%uint63.

    Definition compare (a b : OverloadableOperator) : comparison :=
      PrimInt63.compare (prim_tag a) (prim_tag b).
  End compare.

End OverloadableOperator.
#[global] Instance OverloadableOperator_compare : Compare OverloadableOperator := OverloadableOperator.compare.

#[global] Instance function_qualifier_compare : Compare function_qualifiers.t := function_qualifiers.compare.

Module atomic_name.
  #[prefix="", only(tag)] derive atomic_name_.
  #[global] Arguments tag {_} & _ : assert.
  Section compare.
    Context {type Expr : Set}.
    Context (compareT : type -> type -> comparison).
    #[local] Notation atomic_name := (atomic_name_ type).
    #[local] Notation tag := (@tag type).

    Record box_Nfunction : Set := Box_Nfunction {
      box_Nfunction_0 : function_qualifiers.t;
      box_Nfunction_1 : ident;
      box_Nfunction_2 : list type;
    }.
    Definition box_Nfunction_compare (b1 b2 : box_Nfunction) : comparison :=
      compare_lex (function_qualifiers.compare b1.(box_Nfunction_0) b2.(box_Nfunction_0)) $ fun _ =>
      compare_lex (PrimString.compare b1.(box_Nfunction_1) b2.(box_Nfunction_1)) $ fun _ =>
      List.compare compareT b1.(box_Nfunction_2) b2.(box_Nfunction_2).

    Record box_Nop : Set := Box_Nop {
      box_Nop_0 : function_qualifiers.t;
      box_Nop_1 : OverloadableOperator;
      box_Nop_2 : list type
    }.
    Definition box_Nop_compare (b1 b2 : box_Nop) : comparison :=
      compare_lex (function_qualifiers.compare b1.(box_Nop_0) b2.(box_Nop_0)) $ fun _ =>
      compare_lex (OverloadableOperator.compare b1.(box_Nop_1) b2.(box_Nop_1)) $ fun _ =>
      List.compare compareT b1.(box_Nop_2) b2.(box_Nop_2).

    Record box_Nop_conv : Set := Box_Nop_conv {
      box_Nop_conv_0 : function_qualifiers.t ;
      box_Nop_conv_1 : type
    }.
    Definition box_Nop_conv_compare (b1 b2 : box_Nop_conv) : comparison :=
      compare_lex (function_qualifiers.compare b1.(box_Nop_conv_0) b2.(box_Nop_conv_0)) $ fun _ =>
      compareT b1.(box_Nop_conv_1) b2.(box_Nop_conv_1).

    Record box_Nop_lit : Set := Box_Nop_lit {
                                    box_Nop_lit_0 : ident ;
                                    box_Nop_lit_1 : list type
                                  }.
    Definition box_Nop_lit_compare (b1 b2 : box_Nop_lit) : comparison :=
      compare_lex (PrimString.compare b1.(box_Nop_lit_0) b2.(box_Nop_lit_0)) $ fun _ =>
          List.compare compareT b1.(box_Nop_lit_1) b2.(box_Nop_lit_1).

    Definition car (t : positive) : Set :=
      match t with
      | 1 => ident
      | 2 => box_Nfunction
      | 3 => list type
      | 4 => unit
      | 5 => box_Nop
      | 6 => box_Nop_conv
      | 7 => box_Nop_lit
      | 8 => N
      | 9 => unit
      | 10 => ident
      | 11 => ident
      | _ => PrimString.string
      end.
    Definition data (p : atomic_name) : car (tag p) :=
      match p with
      | Nid id => id
      | Nfunction qs f ts => Box_Nfunction qs f ts
      | Nctor ts => ts
      | Ndtor => tt
      | Nop a b c => Box_Nop a b c
      | Nop_conv a b => Box_Nop_conv a b
      | Nop_lit a b => Box_Nop_lit a b
      | Nanon n => n
      | Nanonymous => tt
      | Nfirst_decl n => n
      | Nfirst_child n => n
      | Nunsupported_atomic msg => msg
      end.
    Definition compare_data (t : positive) : car t -> car t -> comparison :=
      match t with
      | 1 => PrimString.compare
      | 2 => box_Nfunction_compare
      | 3 => List.compare compareT
      | 4 => _compare
      | 5 => box_Nop_compare
      | 6 => box_Nop_conv_compare
      | 7 => box_Nop_lit_compare
      | 8 => N.compare
      | 9 => _compare
      | 10 => PrimString.compare
      | 11 => PrimString.compare
      | _ => PrimString.compare
      end.

    #[local] Notation compare_ctor := (compare_ctor tag car data compare_data).

    #[local] Notation compare_tag := (compare_tag tag).

    #[local] Notation COMP e := (compare_ctor (Reduce (tag (e : atomic_name))) (fun _ => Reduce (data (e : atomic_name)))) (only parsing).



    Definition compare (p : atomic_name) : atomic_name -> comparison :=
      match p with
      | Nid i => COMP (Nid i : atomic_name)
      | Nfunction qs f ts => COMP (Nfunction qs f ts)
      | Nctor ts => COMP (Nctor ts)
      | Ndtor => COMP (Ndtor : atomic_name)
      | Nop a b c => COMP (Nop a b c)
      | Nop_conv a b => COMP (Nop_conv a b)
      | Nop_lit a b => COMP (Nop_lit a b)
      | Nanon n => COMP (Nanon n : atomic_name)
      | Nanonymous => COMP (Nanonymous : atomic_name)
      | Nfirst_decl n => COMP (Nfirst_decl n : atomic_name)
      | Nfirst_child n => COMP (Nfirst_child n : atomic_name)
      | Nunsupported_atomic msg => COMP (Nunsupported_atomic msg : atomic_name)
      end.
  End compare.

End atomic_name.
#[global] Instance atomic_name_compare {A : Set} `{!Compare A}
  : Compare (atomic_name_ A) := atomic_name.compare compare.
#[global] Instance atomic_name_comparison {A : Set} `{!@Comparison A cmpA}
  : Comparison (atomic_name.compare cmpA).
Proof. Admitted.
#[global] Instance atomic_name_leibniz_comparison {A : Set} `{!@Comparison A cmpA} `{LeibnizComparison cmpA}
  : LeibnizComparison (atomic_name.compare cmpA).
Proof. Admitted.

Module Cast.
  Section compare.
    Context (compareT : type -> type -> comparison).

    #[local] Canonical type_comparator :=
      {| _car := type
      ; _compare := compareT |}.

    Definition tag (c : Cast) : positive :=
      match c with
      | Cdependent _ => 1
      | Cbitcast _ => 2
      | Clvaluebitcast _ => 3
      | Cl2r => 4
      | Cl2r_bitcast _ => 23
      | Cnoop _ => 5
      | Carray2ptr => 6
      | Cfun2ptr => 7
      | Cint2ptr _ => 8
      | Cptr2int _ => 9
      | Cptr2bool => 10
      | Cintegral _ => 11
      | Cint2bool => 12
      | Cfloat2int _ => 13
      | Cint2float _ => 25
      | Cfloat _ => 24
      | Cnull2ptr _ => 14
      | Cnull2memberptr _ => 15
      | Cbuiltin2fun _ => 16
      | C2void => 17
      | Cctor _ => 18
      | Cuser => 19
      | Cdynamic _ => 20
      | Cderived2base _ _ => 21
      | Cbase2derived _ _ => 22
      | Cunsupported _ _ => 26
      end.
    Definition car (t : positive) : Set :=
      match t with
      | 1 | 2 | 3 => type
      | 4 => unit
      | 5 => type
      | 6 | 7 => unit
      | 8 | 9 => type
      | 10 | 12 => unit
      | 11 | 13 | 14 | 15 | 16 => type
      | 17 => unit
      | 18 => type
      | 19 => unit
      | 20 => type
      | 21 | 22 => list type * type
      | 23 | 24 | 25 => type
      | 26 => bs * type
      | _ => unit
      end.
    Definition data (c : Cast) : car (tag c) :=
      match c with
      | Cdependent t
      | Cbitcast t
      | Clvaluebitcast t => t
      | Cl2r => tt
      | Cl2r_bitcast t => t
      | Cnoop t => t
      | Carray2ptr
      | Cfun2ptr => tt
      | Cint2ptr t
      | Cptr2int t => t
      | Cptr2bool => ()
      | Cderived2base ns t | Cbase2derived ns t => (ns, t)
      | Cintegral t => t
      | Cint2bool => ()
      | Cfloat2int t
      | Cint2float t
      | Cfloat t
      | Cnull2ptr t
      | Cnull2memberptr t
      | Cbuiltin2fun t
      | Cctor t => t
      | Cuser => tt
      | Cdynamic t => t
      | Cunsupported err t => (err, t)
      | _ => ()
      end.
    Definition compare_data (t : positive) : car t -> car t -> comparison :=
      match t as t return car t -> car t -> comparison with
      | 1 | 2 | 3 => compareT
      | 4 => compare_unit
      | 5 => compareT
      | 6 | 7 => compare_unit
      | 8 | 9 => compareT
      | 10 | 12 => compare_unit
      | 11 | 13 | 14 | 15 | 16 => compareT
      | 17 => compare_unit
      | 18 => compareT
      | 19 => compare_unit
      | 20 => compareT
      | 21 => _compare | 22 => _compare
      | 23 => _compare | 24 => _compare
      | 25 => _compare
      | 26 => _compare
      | _ => compare_unit
      end.

    #[local] Notation TAG := tag.
    #[local] Notation compare_ctor := (compare_ctor TAG car data).
    #[local] Notation compare_tag := (compare_tag TAG).
    #[local] Notation COMP X :=
      (compare_ctor compare_data (Reduce (TAG X)) (fun _ => Reduce (data X))) (only parsing).
    Definition compare_body (c : Cast) : Cast -> comparison :=
      match c with
      | Cdependent t => COMP (Cdependent t : Cast)
      | Cbitcast t => COMP (Cbitcast t : Cast)
      | Clvaluebitcast t => COMP (Clvaluebitcast t : Cast)
      | Cl2r => COMP (Cl2r : Cast)
      | Cl2r_bitcast t => COMP (Cl2r_bitcast t : Cast)
      | Cnoop t => COMP (Cnoop t : Cast)
      | Carray2ptr => compare_tag (Reduce (TAG Carray2ptr))
      | Cfun2ptr => compare_tag (Reduce (TAG Cfun2ptr))
      | Cint2ptr t => COMP (Cint2ptr t : Cast)
      | Cptr2int t => COMP (Cptr2int t : Cast)
      | Cptr2bool => compare_tag (Reduce (TAG Cptr2bool))
      | Cderived2base ns t => COMP (Cderived2base ns t : Cast)
      | Cbase2derived ns t => COMP (Cbase2derived ns t : Cast)
      | Cintegral t => COMP (Cintegral t : Cast)
      | Cint2bool => compare_tag (Reduce (TAG Cint2bool))
      | Cfloat2int t => COMP (Cfloat2int t : Cast)
      | Cint2float t => COMP (Cint2float t : Cast)
      | Cfloat t => COMP (Cfloat t : Cast)
      | Cnull2ptr t => COMP (Cnull2ptr t : Cast)
      | Cnull2memberptr t => COMP (Cnull2memberptr t : Cast)
      | Cbuiltin2fun t => COMP (Cbuiltin2fun t : Cast)
      | Cctor t => COMP (Cctor t : Cast)
      | C2void => compare_tag (Reduce (TAG C2void))
      | Cuser => COMP (Cuser : Cast)
      | Cdynamic cls => COMP (Cdynamic cls : Cast)
      | Cunsupported err t => COMP (Cunsupported err t : Cast)
      end.
  End compare.

End Cast.

Module name.
  Section compare_body.
    Context (compareN : name -> name -> comparison).
    Context (compareT : type -> type -> comparison).
    Context (compareE : Expr -> Expr -> comparison).

    Record box_Ninst : Set := Box_Ninst {
      box_Ninst_0 : name;
      box_Ninst_1 : list temp_arg;
    }.
    Definition box_Ninst_compare (b1 b2 : box_Ninst) : comparison :=
      compare_lex (compareN b1.(box_Ninst_0) b2.(box_Ninst_0)) $ fun _ =>
      List.compare (temp_arg.compare compareN compareT compareE) b1.(box_Ninst_1) b2.(box_Ninst_1).

    Record box_Nscoped : Set := Box_Nscoped {
      box_Nscoped_0 : name;
      box_Nscoped_1 : atomic_name; (* compare first b/c they are cheap and very discriminating *)
    }.
    Definition box_Nscoped_compare (b1 b2 : box_Nscoped) : comparison :=
      compare_lex (atomic_name.compare compareT b1.(box_Nscoped_1) b2.(box_Nscoped_1)) $ fun _ =>
      compareN b1.(box_Nscoped_0) b2.(box_Nscoped_0).

    Definition tag (n : name) : positive :=
      match n with
      | Ninst _ _ => 1
      | Nglobal _ => 2
      | Ndependent _ => 3
      | Nscoped _ _ => 4
      | _ => 5
      end.
    Definition car (t : positive) : Set :=
      match t with
      | 1 => box_Ninst
      | 2 => atomic_name
      | 3 => type
      | 4 => box_Nscoped
      | _ => PrimString.string
      end.
    Definition data (n : name) : car (tag n) :=
      match n with
      | Ninst n args => Box_Ninst n args
      | Nglobal c => c
      | Ndependent t => t
      | Nscoped n c => Box_Nscoped n c
      | Nunsupported msg => msg
      end.
    Definition compare_data (t : positive) : car t -> car t -> comparison :=
      match t with
      | 1 => box_Ninst_compare
      | 2 => atomic_name.compare compareT
      | 3 => compareT
      | 4 => box_Nscoped_compare
      | _ => PrimString.compare
      end.

    #[local] Notation compare_ctor := (compare_ctor tag car data compare_data).
    Definition compare_body (n : name) : name -> comparison :=
      match n with
      | Ninst t xs => compare_ctor (Reduce (tag (Ninst t xs))) (fun _ => Reduce (data (Ninst t xs)))
      | Nglobal c => compare_ctor (Reduce (tag (Nglobal c))) (fun _ => Reduce (data (Nglobal c)))
      | Ndependent t => compare_ctor (Reduce (tag (Ndependent t))) (fun _ => Reduce (data (Ndependent t)))
      | Nscoped n c => compare_ctor (Reduce (tag (Nscoped n c))) (fun _ => Reduce (data (Nscoped n c)))
      | Nunsupported msg => compare_ctor (Reduce (tag (Nunsupported msg))) (fun _ => Reduce (data (Nunsupported msg)))
      end.
  End compare_body.
End name.

Module type.
  Section compare_body.
    Context (compareN : name -> name -> comparison).
    Context (compareT : type -> type -> comparison).
    Context (compareE : Expr -> Expr -> comparison).


    Record box_Tresult_unop : Set := Box_Tresult_unop {
      box_Tresult_unop_0 : RUnOp;
      box_Tresult_unop_1 : type;
    }.
    Definition box_Tresult_unop_compare (b1 b2 : box_Tresult_unop) : comparison :=
      compare_lex (RUnOp.compare b1.(box_Tresult_unop_0) b2.(box_Tresult_unop_0)) $ fun _ =>
      compareT b1.(box_Tresult_unop_1) b2.(box_Tresult_unop_1).

    Record box_Tresult_binop : Set := Box_Tresult_binop {
      box_Tresult_binop_0 : RBinOp;
      box_Tresult_binop_1 : type;
      box_Tresult_binop_2 : type;
    }.
    Definition box_Tresult_binop_compare (b1 b2 : box_Tresult_binop) : comparison :=
      compare_lex (RBinOp.compare b1.(box_Tresult_binop_0) b2.(box_Tresult_binop_0)) $ fun _ =>
      compare_lex (compareT b1.(box_Tresult_binop_1) b2.(box_Tresult_binop_1)) $ fun _ =>
      compareT b1.(box_Tresult_binop_2) b2.(box_Tresult_binop_2).

    Record box_Tresult_call : Set := Box_Tresult_call {
      box_Tresult_call_0 : name;
      box_Tresult_call_1 : list type;
    }.
    Definition box_Tresult_call_compare (b1 b2 : box_Tresult_call) : comparison :=
      compare_lex (compareN b1.(box_Tresult_call_0) b2.(box_Tresult_call_0)) $ fun _ =>
      List.compare compareT b1.(box_Tresult_call_1) b2.(box_Tresult_call_1).

    Record box_Tresult_member_call : Set := Box_Tresult_member_call {
      box_Tresult_member_call_0 : name;
      box_Tresult_member_call_1 : type;
      box_Tresult_member_call_2 : list type;
    }.
    Definition box_Tresult_member_call_compare (b1 b2 : box_Tresult_member_call) : comparison :=
      compare_lex (compareN b1.(box_Tresult_member_call_0) b2.(box_Tresult_member_call_0)) $ fun _ =>
      compare_lex (compareT b1.(box_Tresult_member_call_1) b2.(box_Tresult_member_call_1)) $ fun _ =>
      List.compare compareT b1.(box_Tresult_member_call_2) b2.(box_Tresult_member_call_2).

    Record box_Tresult_parenlist : Set := Box_Tresult_parenlist {
      box_Tresult_parenlist_0 : type;
      box_Tresult_parenlist_1 : list type;
    }.
    Definition box_Tresult_parenlist_compare (b1 b2 : box_Tresult_parenlist) : comparison :=
      compare_lex (compareT b1.(box_Tresult_parenlist_0) b2.(box_Tresult_parenlist_0)) $ fun _ =>
      List.compare compareT b1.(box_Tresult_parenlist_1) b2.(box_Tresult_parenlist_1).

    Record box_Tresult_member : Set := Box_Tresult_member {
      box_Tresult_member_0 : type;
      box_Tresult_member_1 : name;
    }.
    Definition box_Tresult_member_compare (b1 b2 : box_Tresult_member) : comparison :=
      compare_lex (compareT b1.(box_Tresult_member_0) b2.(box_Tresult_member_0)) $ fun _ =>
      compareN b1.(box_Tresult_member_1) b2.(box_Tresult_member_1).

    Record box_Tnum : Set := Box_Tnum {
      box_Tnum_0 : int_rank.t;
      box_Tnum_1 : signed;
    }.

    Definition box_Tnum_compare (b1 b2 : box_Tnum) : comparison :=
      compare_lex (int_rank.compare b1.(box_Tnum_0) b2.(box_Tnum_0)) $ fun _ =>
      signed.compare b1.(box_Tnum_1) b2.(box_Tnum_1).

    Record box_Tarray : Set := Box_Tarray {
      box_Tarray_0 : type;
      box_Tarray_1 : N;
    }.
    Definition box_Tarray_compare (b1 b2 : box_Tarray) : comparison :=
      compare_lex (compareT b1.(box_Tarray_0) b2.(box_Tarray_0)) $ fun _ =>
      N.compare b1.(box_Tarray_1) b2.(box_Tarray_1).

    Record box_Tvariable_array : Set := Box_Tvariable_array {
      box_Tvariable_array_0 : type;
      box_Tvariable_array_1 : Expr;
    }.
    Definition box_Tvariable_array_compare (b1 b2 : box_Tvariable_array) : comparison :=
      compare_lex (compareT b1.(box_Tvariable_array_0) b2.(box_Tvariable_array_0)) $ fun _ =>
      compareE b1.(box_Tvariable_array_1) b2.(box_Tvariable_array_1).

    Record box_Tmember_pointer : Set := Box_Tmember_pointer {
      box_Tmember_pointer_0 : type;
      box_Tmember_pointer_1 : type;
    }.
    Definition box_Tmember_pointer_compare (b1 b2 : box_Tmember_pointer) : comparison :=
      compare_lex (compareT b1.(box_Tmember_pointer_0) b2.(box_Tmember_pointer_0)) $ fun _ =>
      compareT b1.(box_Tmember_pointer_1) b2.(box_Tmember_pointer_1).

    Record box_Tqualified : Set := Box_Tqualified {
      box_Tqualified_0 : type_qualifiers;
      box_Tqualified_1 : type;
    }.
    Definition box_Tqualified_compare (b1 b2 : box_Tqualified) : comparison :=
      compare_lex (type_qualifiers.compare b1.(box_Tqualified_0) b2.(box_Tqualified_0)) $ fun _ =>
      compareT b1.(box_Tqualified_1) b2.(box_Tqualified_1).

    Record box_Tarch : Set := Box_Tarch {
      box_Tarch_0 : option bitsize;
      box_Tarch_1 : PrimString.string;
    }.
    Definition box_Tarch_compare (b1 b2 : box_Tarch) : comparison :=
      compare_lex (option.compare bitsize.compare b1.(box_Tarch_0) b2.(box_Tarch_0)) $ fun _ =>
      PrimString.compare b1.(box_Tarch_1) b2.(box_Tarch_1).

    Import PrimInt63.

    Definition prim_tagFT (ft : float_type.t) : PrimInt63.int :=
      match ft with
      | float_type.Ffloat => 1
      | float_type.Fdouble => 2
      | float_type.Flongdouble => 3
      | float_type.Ffloat16 => 4
      | float_type.Ffloat128 => 5
      end%uint63.

    #[local] Definition tag_direct (i : PrimInt63.int) : _ + positive :=
      inl i.
    Arguments tag_direct _%_uint63.

    #[local] Definition FIRST_INT_TAG : PrimInt63.int :=
      3.
    #[local] Definition FIRST_CHAR_TAG : PrimInt63.int :=
      Evaluate (PrimInt63.add FIRST_INT_TAG $ PrimInt63.mul 2%uint63 (PrimInt63.add 1 $ int_rank.prim_tag int_rank.I128)).
    #[local] Definition FIRST_FLOAT_TAG : PrimInt63.int :=
      Evaluate (PrimInt63.add FIRST_CHAR_TAG (prim_tagFT float_type.Ffloat128)).

    #[local] Notation "a + b" := (PrimInt63.add a b) : uint63_scope.
    #[local] Notation "a * b" := (PrimInt63.mul a b) : uint63_scope.

    Definition car (p : positive) : Set :=
      match p with
      | 1 | 2 => name
      | 3 | 4 | 5 => type
      | 6 => box_Tqualified
      | 7 => box_Tarray
      | 8 => type
      | 9 => box_Tvariable_array
      | 10 => function_type
      | 11 => box_Tmember_pointer
      | 12 => box_Tarch
      | 13 | 14 => Expr
      | 15 | 16 => ident
      | 17 => name
      | 18 => box_Tresult_unop
      | 19 => box_Tresult_binop
      | 20 => box_Tresult_call
      | 21 => box_Tresult_member_call
      | 22 => box_Tresult_parenlist
      | 23 => box_Tresult_member
      | _ => PrimString.string
      end.

    (*
    Definition tag' (t : type) : PrimInt63.int + positive :=
      match t with
      | Tnum r Unsigned => tag_direct (FIRST_INT_TAG + int_rank.prim_tag r * 2)%uint63
      | Tnum r Signed => tag_direct (FIRST_INT_TAG + int_rank.prim_tag r * 2 + 1)%uint63
      | Tchar_ ct => tag_direct (FIRST_CHAR_TAG + char_type.prim_tag ct)%uint63
      | Tfloat_ ft => tag_direct (FIRST_FLOAT_TAG + prim_tagFT ft)
      | Tvoid => tag_direct 0
      | Tnullptr => tag_direct 1
      | Tbool => tag_direct 2
      | Tnamed _ => inr 1
      | Tenum _ => inr 2
      | Tptr _ => inr 3
      | Tref _ => inr 4
      | Trv_ref _ => inr 5
      | Tqualified _ _ => inr 6
      | Tarray _ _ => inr 7
      | Tincomplete_array _ => inr 8
      | Tvariable_array _ _ => inr 9
      | Tfunction _ => inr 10
      | Tmember_pointer _ _ => inr 11
      | Tarch _ _ => inr 12
      | Tdecltype _ => inr 13
      | Texprtype _ => inr 14
      | Tparam _ => inr 15
      | Tresult_param _ => inr 16
      | Tresult_global _ => inr 17
      | Tresult_unop _ _ => inr 18
      | Tresult_binop _ _ _ => inr 19
      | Tresult_call _ _ => inr 20
      | Tresult_member_call _ _ _ => inr 21
      | Tresult_parenlist _ _ => inr 22
      | Tresult_member _ _ => inr 23
      | Tunsupported _ => inr 24
      end.
      *)

    Definition data {T} (t : type) (k : int -> T) (kp : forall p, car p -> T) : T :=
      match t with
      | Tnum r Unsigned => k (FIRST_INT_TAG + int_rank.prim_tag r * 2)%uint63
      | Tnum r Signed => k (FIRST_INT_TAG + int_rank.prim_tag r * 2 + 1)%uint63
      | Tchar_ ct => k (FIRST_CHAR_TAG + char_type.prim_tag ct)%uint63
      | Tfloat_ ft => k (FIRST_FLOAT_TAG + prim_tagFT ft)%uint63
      | Tvoid => k 0%uint63
      | Tnullptr => k 1%uint63
      | Tbool => k 2%uint63
      | Tnamed n => kp 1 n
      | Tenum n => kp 2 n
      | Tptr t => kp 3 t
      | Tref t => kp 4 t
      | Trv_ref t => kp 5 t
      | Tqualified q t => kp 6 $ Box_Tqualified q t
      | Tarray t n => kp 7 $ Box_Tarray t n
      | Tincomplete_array t => kp 8 t
      | Tvariable_array t e => kp 9 $ Box_Tvariable_array t e
      | Tfunction ft => kp 10 ft
      | Tmember_pointer a b => kp 11 $ Box_Tmember_pointer a b
      | Tarch a b => kp 12 $ Box_Tarch a b
      | Tdecltype e => kp 13 e
      | Texprtype e => kp 14 e
      | Tparam n => kp 15 n
      | Tresult_param n => kp 16 n
      | Tresult_global n => kp 17 n
      | Tresult_unop a b => kp 18 $ Box_Tresult_unop a b
      | Tresult_binop a b c => kp 19 $ Box_Tresult_binop a b c
      | Tresult_call a b => kp 20 $ Box_Tresult_call a b
      | Tresult_member_call a b c => kp 21 $ Box_Tresult_member_call a b c
      | Tresult_parenlist a b => kp 22 $ Box_Tresult_parenlist a b
      | Tresult_member a b => kp 23 $ Box_Tresult_member a b
      | Tauto => k 3%uint63
      | Tunsupported msg => kp 24 msg
      end.

    Definition compare_data (p : positive) : car p -> car p -> comparison :=
      match p as p return car p -> car p -> comparison with
      | 1 | 2 => compareN
      | 3 | 4 | 5 => compareT
      | 6 => box_Tqualified_compare
      | 7 => box_Tarray_compare
      | 8 => compareT
      | 9 => box_Tvariable_array_compare
      | 10 => function_type.compare compareT
      | 11 => box_Tmember_pointer_compare
      | 12 => box_Tarch_compare
      | 13 | 14 => compareE
      | 15 | 16 => PrimString.compare
      | 17 => compareN
      | 18 => box_Tresult_unop_compare
      | 19 => box_Tresult_binop_compare
      | 20 => box_Tresult_call_compare
      | 21 => box_Tresult_member_call_compare
      | 22 => box_Tresult_parenlist_compare
      | 23 => box_Tresult_member_compare
      | _ => PrimString.compare
      end.

    Definition compare_body' (a b : positive) (av : car a) : car b -> comparison :=
      match Pos.compare a b as CMP return Pos.compare a b = CMP -> _ with
      | Eq => fun pf =>
               match numbers.Pos.compare_eq _ _ pf with
               | eq_refl => compare_data _ av
               end
      | Lt => fun _ _ => Lt
      | Gt => fun _ _ => Gt
      end eq_refl.

    Definition compare_body (a b : type) : comparison :=
      data a (fun a => data b (fun b => Uint63.compare a b)
                         (fun _ _ => Lt))
        (fun a ad => data b (fun b => Gt)
                       (fun b bd => compare_body' a b ad bd)).
  End compare_body.

End type.

Module Expr.
  Section compare_body.
    Context (compareN : name -> name -> comparison).
    Context (compareT : type -> type -> comparison).
    Context (compareC : Cast -> Cast -> comparison).
    Context (compareE : Expr -> Expr -> comparison).
    Context (compareS : Stmt -> Stmt -> comparison).

    Record box_Eunresolved_unop : Set := Box_Eunresolved_unop {
      box_Eunresolved_unop_0 : RUnOp;
      box_Eunresolved_unop_1 : Expr;
    }.
    Definition box_Eunresolved_unop_compare (b1 b2 : box_Eunresolved_unop) : comparison :=
      compare_lex (RUnOp.compare b1.(box_Eunresolved_unop_0) b2.(box_Eunresolved_unop_0)) $ fun _ =>
      compareE b1.(box_Eunresolved_unop_1) b2.(box_Eunresolved_unop_1).

    Record box_Eunresolved_binop : Set := Box_Eunresolved_binop {
      box_Eunresolved_binop_0 : RBinOp;
      box_Eunresolved_binop_1 : Expr;
      box_Eunresolved_binop_2 : Expr;
    }.
    Definition box_Eunresolved_binop_compare (b1 b2 : box_Eunresolved_binop) : comparison :=
      compare_lex (RBinOp.compare b1.(box_Eunresolved_binop_0) b2.(box_Eunresolved_binop_0)) $ fun _ =>
      compare_lex (compareE b1.(box_Eunresolved_binop_1) b2.(box_Eunresolved_binop_1)) $ fun _ =>
      compareE b1.(box_Eunresolved_binop_2) b2.(box_Eunresolved_binop_2).

    Record box_Eunresolved_call : Set := Box_Eunresolved_call {
      box_Eunresolved_call_0 : name;
      box_Eunresolved_call_1 : list Expr;
    }.
    Definition box_Eunresolved_call_compare (b1 b2 : box_Eunresolved_call) : comparison :=
      compare_lex (compareN b1.(box_Eunresolved_call_0) b2.(box_Eunresolved_call_0)) $ fun _ =>
      List.compare compareE b1.(box_Eunresolved_call_1) b2.(box_Eunresolved_call_1).

    Record box_Eunresolved_member_call : Set := Box_Eunresolved_member_call {
      box_Eunresolved_member_call_0 : name;
      box_Eunresolved_member_call_1 : Expr;
      box_Eunresolved_member_call_2 : list Expr;
    }.
    Definition box_Eunresolved_member_call_compare (b1 b2 : box_Eunresolved_member_call) : comparison :=
      compare_lex (compareN b1.(box_Eunresolved_member_call_0) b2.(box_Eunresolved_member_call_0)) $ fun _ =>
      compare_lex (compareE b1.(box_Eunresolved_member_call_1) b2.(box_Eunresolved_member_call_1)) $ fun _ =>
      List.compare compareE b1.(box_Eunresolved_member_call_2) b2.(box_Eunresolved_member_call_2).

    Record box_Eunresolved_parenlist : Set := Box_Eunresolved_parenlist {
      box_Eunresolved_parenlist_0 : option type;
      box_Eunresolved_parenlist_1 : list Expr;
    }.
    Definition box_Eunresolved_parenlist_compare (b1 b2 : box_Eunresolved_parenlist) : comparison :=
      compare_lex (option.compare compareT b1.(box_Eunresolved_parenlist_0) b2.(box_Eunresolved_parenlist_0)) $ fun _ =>
      List.compare compareE b1.(box_Eunresolved_parenlist_1) b2.(box_Eunresolved_parenlist_1).

    Record box_Eunresolved_member : Set := Box_Eunresolved_member {
      box_Eunresolved_member_0 : Expr;
      box_Eunresolved_member_1 : name;
    }.
    Definition box_Eunresolved_member_compare (b1 b2 : box_Eunresolved_member) : comparison :=
      compare_lex (compareE b1.(box_Eunresolved_member_0) b2.(box_Eunresolved_member_0)) $ fun _ =>
      compareN b1.(box_Eunresolved_member_1) b2.(box_Eunresolved_member_1).

    Record box_Evar : Set := Box_Evar {
      box_Evar_0 : localname;
      box_Evar_1 : type;
    }.
    Definition box_Evar_compare (b1 b2 : box_Evar) : comparison :=
      compare_lex (PrimString.compare b1.(box_Evar_0) b2.(box_Evar_0)) $ fun _ =>
      compareT b1.(box_Evar_1) b2.(box_Evar_1).

    Record box_Eenum_const : Set := Box_Eenum_const {
      box_Eenum_const_0 : name;
      box_Eenum_const_1 : ident;
    }.
    Definition box_Eenum_const_compare (b1 b2 : box_Eenum_const) : comparison :=
      compare_lex (compareN b1.(box_Eenum_const_0) b2.(box_Eenum_const_0)) $ fun _ =>
      PrimString.compare b1.(box_Eenum_const_1) b2.(box_Eenum_const_1).

    Record box_Eglobal : Set := Box_Eglobal {
      box_Eglobal_0 : name;
      box_Eglobal_1 : type;
    }.
    Definition box_Eglobal_compare (b1 b2 : box_Eglobal) : comparison :=
      compare_lex (compareN b1.(box_Eglobal_0) b2.(box_Eglobal_0)) $ fun _ =>
      compareT b1.(box_Eglobal_1) b2.(box_Eglobal_1).

    Record box_Echar : Set := Box_Echar {
      box_Echar_0 : N;
      box_Echar_1 : type;
    }.
    Definition box_Echar_compare (b1 b2 : box_Echar) : comparison :=
      compare_lex (N.compare b1.(box_Echar_0) b2.(box_Echar_0)) $ fun _ =>
      compareT b1.(box_Echar_1) b2.(box_Echar_1).

    Record box_Estring : Set := Box_Estring {
      box_Estring_0 : literal_string.t;
      box_Estring_1 : type;
    }.
    Definition box_Estring_compare (b1 b2 : box_Estring) : comparison :=
      compare_lex (literal_string.compare b1.(box_Estring_0) b2.(box_Estring_0)) $ fun _ =>
      compareT b1.(box_Estring_1) b2.(box_Estring_1).

    Record box_Eint : Set := Box_Eint {
      box_Eint_0 : Z;
      box_Eint_1 : type;
    }.
    Definition box_Eint_compare (b1 b2 : box_Eint) : comparison :=
      compare_lex (Z.compare b1.(box_Eint_0) b2.(box_Eint_0)) $ fun _ =>
      compareT b1.(box_Eint_1) b2.(box_Eint_1).

    Record box_Eunop : Set := Box_Eunop {
      box_Eunop_0 : UnOp;
      box_Eunop_1 : Expr;
      box_Eunop_2 : type;
    }.
    Definition box_Eunop_compare (b1 b2 : box_Eunop) : comparison :=
      compare_lex (UnOp.compare b1.(box_Eunop_0) b2.(box_Eunop_0)) $ fun _ =>
      compare_lex (compareE b1.(box_Eunop_1) b2.(box_Eunop_1)) $ fun _ =>
      compareT b1.(box_Eunop_2) b2.(box_Eunop_2).

    Record box_Ebinop : Set := Box_Ebinop {
      box_Ebinop_0 : BinOp;
      box_Ebinop_1 : Expr;
      box_Ebinop_2 : Expr;
      box_Ebinop_3 : type;
    }.
    Definition box_Ebinop_compare (b1 b2 : box_Ebinop) : comparison :=
      compare_lex (BinOp.compare b1.(box_Ebinop_0) b2.(box_Ebinop_0)) $ fun _ =>
      compare_lex (compareE b1.(box_Ebinop_1) b2.(box_Ebinop_1)) $ fun _ =>
      compare_lex (compareE b1.(box_Ebinop_2) b2.(box_Ebinop_2)) $ fun _ =>
      compareT b1.(box_Ebinop_3) b2.(box_Ebinop_3).

    Record box_Ederef : Set := Box_Ederef {
      box_Ederef_0 : Expr;
      box_Ederef_1 : type;
    }.
    Definition box_Ederef_compare (b1 b2 : box_Ederef) : comparison :=
      compare_lex (compareE b1.(box_Ederef_0) b2.(box_Ederef_0)) $ fun _ =>
      compareT b1.(box_Ederef_1) b2.(box_Ederef_1).

    Record box_Eassign : Set := Box_Eassign {
      box_Eassign_0 : Expr;
      box_Eassign_1 : Expr;
      box_Eassign_2 : type;
    }.
    Definition box_Eassign_compare (b1 b2 : box_Eassign) : comparison :=
      compare_lex (compareE b1.(box_Eassign_0) b2.(box_Eassign_0)) $ fun _ =>
      compare_lex (compareE b1.(box_Eassign_1) b2.(box_Eassign_1)) $ fun _ =>
      compareT b1.(box_Eassign_2) b2.(box_Eassign_2).

    Record box_Eseqand : Set := Box_Eseqand {
      box_Eseqand_0 : Expr;
      box_Eseqand_1 : Expr;
    }.
    Definition box_Eseqand_compare (b1 b2 : box_Eseqand) : comparison :=
      compare_lex (compareE b1.(box_Eseqand_0) b2.(box_Eseqand_0)) $ fun _ =>
      compareE b1.(box_Eseqand_1) b2.(box_Eseqand_1).

    Record box_Ecall : Set := Box_Ecall {
      box_Ecall_0 : Expr;
      box_Ecall_1 : list Expr;
    }.
    Definition box_Ecall_compare (b1 b2 : box_Ecall) : comparison :=
      compare_lex (compareE b1.(box_Ecall_0) b2.(box_Ecall_0)) $ fun _ =>
      List.compare compareE b1.(box_Ecall_1) b2.(box_Ecall_1).

    Record box_Eexplicit_cast : Set := Box_Eexplicit_cast {
      box_Eexplicit_cast_0 : cast_style.t;
      box_Eexplicit_cast_1 : type;
      box_Eexplicit_cast_2 : Expr;
    }.
    Definition box_Eexplicit_cast_compare (b1 b2 : box_Eexplicit_cast) : comparison :=
      compare_lex (_compare b1.(box_Eexplicit_cast_0) b2.(box_Eexplicit_cast_0)) $ fun _ =>
      compare_lex (compareT b1.(box_Eexplicit_cast_1) b2.(box_Eexplicit_cast_1)) $ fun _ =>
      compareE b1.(box_Eexplicit_cast_2) b2.(box_Eexplicit_cast_2).

    Record box_Ecast : Set := Box_Ecast {
      box_Ecast_0 : Cast;
      box_Ecast_1 : Expr;
    }.
    Definition box_Ecast_compare (b1 b2 : box_Ecast) : comparison :=
      compare_lex (compareC b1.(box_Ecast_0) b2.(box_Ecast_0)) $ fun _ =>
      compareE b1.(box_Ecast_1) b2.(box_Ecast_1).

    Record box_Edependent_cast : Set := Box_Edependent_cast {
      box_Edependent_cast_0 : Expr ;
      box_Edependent_cast_1 : type;
    }.
    Definition box_Edependent_cast_compare (b1 b2 : box_Edependent_cast) : comparison :=
      compare_lex (compareE b1.(box_Edependent_cast_0) b2.(box_Edependent_cast_0)) $ fun _ =>
      compareT b1.(box_Edependent_cast_1) b2.(box_Edependent_cast_1).

    Record box_Emember : Set := Box_Emember {
      box_Emember_0 : bool ;
      box_Emember_1 : Expr;
      box_Emember_2 : atomic_name;
      box_Emember_3 : bool;
      box_Emember_4 : type;
    }.
    Definition box_Emember_compare (b1 b2 : box_Emember) : comparison :=
      compare_lex (Bool.compare b1.(box_Emember_0) b2.(box_Emember_0)) $ fun _ =>
      compare_lex (compareE b1.(box_Emember_1) b2.(box_Emember_1)) $ fun _ =>
      compare_lex (atomic_name.compare compareT b1.(box_Emember_2) b2.(box_Emember_2)) $ fun _ =>
      compare_lex (Bool.compare b1.(box_Emember_3) b2.(box_Emember_3)) $ fun _ =>
      compareT b1.(box_Emember_4) b2.(box_Emember_4).

    Record box_Emember_ignore : Set := Box_Emember_ignore {
      box_Emember_ignore_0 : bool ;
      box_Emember_ignore_1 : Expr;
      box_Emember_ignore_2 : Expr;
    }.
    Definition box_Emember_ignore_compare (b1 b2 : box_Emember_ignore) : comparison :=
      compare_lex (Bool.compare b1.(box_Emember_ignore_0) b2.(box_Emember_ignore_0)) $ fun _ =>
      compare_lex (compareE b1.(box_Emember_ignore_1) b2.(box_Emember_ignore_1)) $ fun _ =>
      compareE b1.(box_Emember_ignore_2) b2.(box_Emember_ignore_2).

    Record box_Emember_call : Set := Box_Emember_call {
      box_Emember_call_0 : bool ;
      box_Emember_call_1 : MethodRef;
      box_Emember_call_2 : Expr;
      box_Emember_call_3 : list Expr;
    }.
    Definition box_Emember_call_compare (b1 b2 : box_Emember_call) : comparison :=
      compare_lex (Bool.compare b1.(box_Emember_call_0) b2.(box_Emember_call_0)) $ fun _ =>
      compare_lex (MethodRef.compare compareN compareT compareE b1.(box_Emember_call_1) b2.(box_Emember_call_1)) $ fun _ =>
      compare_lex (compareE b1.(box_Emember_call_2) b2.(box_Emember_call_2)) $ fun _ =>
      List.compare compareE b1.(box_Emember_call_3) b2.(box_Emember_call_3).

    Record box_Eoperator_call : Set := Box_Eoperator_call {
      box_Eoperator_call_0 : OverloadableOperator;
      box_Eoperator_call_1 : operator_impl.t name type;
      box_Eoperator_call_2 : list Expr;
    }.
    Definition box_Eoperator_call_compare (b1 b2 : box_Eoperator_call) : comparison :=
      compare_lex (OverloadableOperator.compare b1.(box_Eoperator_call_0) b2.(box_Eoperator_call_0)) $ fun _ =>
      compare_lex (operator_impl.compare compareN compareT b1.(box_Eoperator_call_1) b2.(box_Eoperator_call_1)) $ fun _ =>
      List.compare compareE b1.(box_Eoperator_call_2) b2.(box_Eoperator_call_2).

    Record box_Esizeof : Set := Box_Esizeof {
      box_Esizeof_0 : type + Expr;
      box_Esizeof_1 : type;
    }.
    Definition box_Esizeof_compare (b1 b2 : box_Esizeof) : comparison :=
      compare_lex (sum.compare compareT compareE b1.(box_Esizeof_0) b2.(box_Esizeof_0)) $ fun _ =>
      compareT b1.(box_Esizeof_1) b2.(box_Esizeof_1).

    Record box_Eoffsetof : Set := Box_Eoffsetof {
      box_Eoffsetof_0 : type;
      box_Eoffsetof_1 : ident;
      box_Eoffsetof_2 : type;
    }.
    Definition box_Eoffsetof_compare (b1 b2 : box_Eoffsetof) : comparison :=
      compare_lex (compareT b1.(box_Eoffsetof_0) b2.(box_Eoffsetof_0)) $ fun _ =>
      compare_lex (PrimString.compare b1.(box_Eoffsetof_1) b2.(box_Eoffsetof_1)) $ fun _ =>
      compareT b1.(box_Eoffsetof_2) b2.(box_Eoffsetof_2).

    Record box_Econstructor : Set := Box_Econstructor {
      box_Econstructor_0 : name;
      box_Econstructor_1 : list Expr;
      box_Econstructor_2 : type;
    }.
    Definition box_Econstructor_compare (b1 b2 : box_Econstructor) : comparison :=
      compare_lex (compareN b1.(box_Econstructor_0) b2.(box_Econstructor_0)) $ fun _ =>
      compare_lex (List.compare compareE b1.(box_Econstructor_1) b2.(box_Econstructor_1)) $ fun _ =>
      compareT b1.(box_Econstructor_2) b2.(box_Econstructor_2).

    Record box_Elambda : Set := Box_Elambda {
      box_Elambda_0 : name;
      box_Elambda_1 : list Expr
    }.
    Definition box_Elambda_compare (b1 b2 : box_Elambda) : comparison :=
      compare_lex (compareN b1.(box_Elambda_0) b2.(box_Elambda_0)) $ fun _ =>
      List.compare compareE b1.(box_Elambda_1) b2.(box_Elambda_1).

    Record box_Eif : Set := Box_Eif {
      box_Eif_0 : Expr;
      box_Eif_1 : Expr;
      box_Eif_2 : Expr;
      box_Eif_3 : type;
    }.
    Definition box_Eif_compare (b1 b2 : box_Eif) : comparison :=
      compare_lex (compareE b1.(box_Eif_0) b2.(box_Eif_0)) $ fun _ =>
      compare_lex (compareE b1.(box_Eif_1) b2.(box_Eif_1)) $ fun _ =>
      compare_lex (compareE b1.(box_Eif_2) b2.(box_Eif_2)) $ fun _ =>
      compareT b1.(box_Eif_3) b2.(box_Eif_3).

    Record box_Eif2 : Set := Box_Eif2 {
      box_Eif2_0 : N;
      box_Eif2_1 : Expr;
      box_Eif2_2 : Expr;
      box_Eif2_3 : Expr;
      box_Eif2_4 : Expr;
      box_Eif2_5 : type;
    }.
    Definition box_Eif2_compare (b1 b2 : box_Eif2) : comparison :=
      compare_lex (N.compare b1.(box_Eif2_0) b2.(box_Eif2_0)) $ fun _ =>
      compare_lex (compareE b1.(box_Eif2_1) b2.(box_Eif2_1)) $ fun _ =>
      compare_lex (compareE b1.(box_Eif2_2) b2.(box_Eif2_2)) $ fun _ =>
      compare_lex (compareE b1.(box_Eif2_3) b2.(box_Eif2_3)) $ fun _ =>
      compare_lex (compareE b1.(box_Eif2_4) b2.(box_Eif2_4)) $ fun _ =>
      compareT b1.(box_Eif2_5) b2.(box_Eif2_5).

    Record box_Einitlist : Set := Box_Einitlist {
      box_Einitlist_0 : list Expr;
      box_Einitlist_1 : option Expr;
      box_Einitlist_2 : type;
    }.
    Definition box_Einitlist_compare (b1 b2 : box_Einitlist) : comparison :=
      compare_lex (List.compare compareE b1.(box_Einitlist_0) b2.(box_Einitlist_0)) $ fun _ =>
      compare_lex (option.compare compareE b1.(box_Einitlist_1) b2.(box_Einitlist_1)) $ fun _ =>
      compareT b1.(box_Einitlist_2) b2.(box_Einitlist_2).

    Record box_Einitlist_union : Set := Box_Einitlist_union {
      box_Einitlist_union_0 : atomic_name_ type;
      box_Einitlist_union_1 : option Expr;
      box_Einitlist_union_2 : type;
    }.
    Definition box_Einitlist_union_compare (b1 b2 : box_Einitlist_union) : comparison :=
      compare_lex (atomic_name.compare compareT b1.(box_Einitlist_union_0) b2.(box_Einitlist_union_0)) $ fun _ =>
      compare_lex (option.compare compareE b1.(box_Einitlist_union_1) b2.(box_Einitlist_union_1)) $ fun _ =>
      compareT b1.(box_Einitlist_union_2) b2.(box_Einitlist_union_2).

    Record box_Enew : Set := Box_Enew {
      box_Enew_0 : name * type;
      box_Enew_1 : list Expr;
      box_Enew_2 : new_form;
      box_Enew_3 : type;
      box_Enew_4 : option Expr;
      box_Enew_5 : option Expr;
    }.
    Definition box_Enew_compare (b1 b2 : box_Enew) : comparison :=
      compare_lex (prod.compare compareN compareT b1.(box_Enew_0) b2.(box_Enew_0)) $ fun _ =>
      compare_lex (List.compare compareE b1.(box_Enew_1) b2.(box_Enew_1)) $ fun _ =>
      compare_lex (new_form.compare b1.(box_Enew_2) b2.(box_Enew_2)) $ fun _ =>
      compare_lex (compareT b1.(box_Enew_3) b2.(box_Enew_3)) $ fun _ =>
      compare_lex (option.compare compareE b1.(box_Enew_4) b2.(box_Enew_4)) $ fun _ =>
      option.compare compareE b1.(box_Enew_5) b2.(box_Enew_5).

    Record box_Edelete : Set := Box_Edelete {
      box_Edelete_0 : bool;
      box_Edelete_1 : name;
      box_Edelete_2 : Expr;
      box_Edelete_3 : type;
    }.
    Definition box_Edelete_compare (b1 b2 : box_Edelete) : comparison :=
      compare_lex (Bool.compare b1.(box_Edelete_0) b2.(box_Edelete_0)) $ fun _ =>
      compare_lex (compareN b1.(box_Edelete_1) b2.(box_Edelete_1)) $ fun _ =>
      compare_lex (compareE b1.(box_Edelete_2) b2.(box_Edelete_2)) $ fun _ =>
      compareT b1.(box_Edelete_3) b2.(box_Edelete_3).

    Record box_Ematerialize_temp : Set := Box_Ematerialize_temp {
      box_Ematerialize_temp_0 : Expr;
      box_Ematerialize_temp_1 : ValCat;
    }.
    Definition box_Ematerialize_temp_compare (b1 b2 : box_Ematerialize_temp) : comparison :=
      compare_lex (compareE b1.(box_Ematerialize_temp_0) b2.(box_Ematerialize_temp_0)) $ fun _ =>
      ValCat.compare b1.(box_Ematerialize_temp_1) b2.(box_Ematerialize_temp_1).

    Record box_Eatomic : Set := Box_Eatomic {
      box_Eatomic_0 : AtomicOp;
      box_Eatomic_1 : list Expr;
      box_Eatomic_2 : type;
    }.
    Definition box_Eatomic_compare (b1 b2 : box_Eatomic) : comparison :=
      compare_lex (AtomicOp.compare b1.(box_Eatomic_0) b2.(box_Eatomic_0)) $ fun _ =>
      compare_lex (List.compare compareE b1.(box_Eatomic_1) b2.(box_Eatomic_1)) $ fun _ =>
      compareT b1.(box_Eatomic_2) b2.(box_Eatomic_2).

    Record box_Epseudo_destructor : Set := Box_Epseudo_destructor {
      box_Epseudo_destructor_0 : bool;
      box_Epseudo_destructor_1 : type;
      box_Epseudo_destructor_2 : Expr;
    }.
    Definition box_Epseudo_destructor_compare (b1 b2 : box_Epseudo_destructor) : comparison :=
      compare_lex (Bool.compare b1.(box_Epseudo_destructor_0) b2.(box_Epseudo_destructor_0)) $ fun _ =>
      compare_lex (compareT b1.(box_Epseudo_destructor_1) b2.(box_Epseudo_destructor_1)) $ fun _ =>
      compareE b1.(box_Epseudo_destructor_2) b2.(box_Epseudo_destructor_2).

    Record box_Earrayloop_init : Set := Box_Earrayloop_init {
      box_Earrayloop_init_0 : N;
      box_Earrayloop_init_1 : Expr;
      box_Earrayloop_init_2 : N;
      box_Earrayloop_init_3 : N;
      box_Earrayloop_init_4 : Expr;
      box_Earrayloop_init_5 : type;
    }.
    Definition box_Earrayloop_init_compare (b1 b2 : box_Earrayloop_init) : comparison :=
      compare_lex (N.compare b1.(box_Earrayloop_init_0) b2.(box_Earrayloop_init_0)) $ fun _ =>
      compare_lex (compareE b1.(box_Earrayloop_init_1) b2.(box_Earrayloop_init_1)) $ fun _ =>
      compare_lex (N.compare b1.(box_Earrayloop_init_2) b2.(box_Earrayloop_init_2)) $ fun _ =>
      compare_lex (N.compare b1.(box_Earrayloop_init_3) b2.(box_Earrayloop_init_3)) $ fun _ =>
      compare_lex (compareE b1.(box_Earrayloop_init_4) b2.(box_Earrayloop_init_4)) $ fun _ =>
      compareT b1.(box_Earrayloop_init_5) b2.(box_Earrayloop_init_5).

    Record box_Eopaque_ref : Set := Box_Eopaque_ref {
      box_Eopaque_ref_0 : N;
      box_Eopaque_ref_1 : type;
    }.
    Definition box_Eopaque_ref_compare (b1 b2 : box_Eopaque_ref) : comparison :=
      compare_lex (N.compare b1.(box_Eopaque_ref_0) b2.(box_Eopaque_ref_0)) $ fun _ =>
      compareT b1.(box_Eopaque_ref_1) b2.(box_Eopaque_ref_1).

    Record box_Eunsupported : Set := Box_Eunsupported {
      box_Eunsupported_0 : PrimString.string;
      box_Eunsupported_1 : type;
    }.
    Definition box_Eunsupported_compare (b1 b2 : box_Eunsupported) : comparison :=
      compare_lex (PrimString.compare b1.(box_Eunsupported_0) b2.(box_Eunsupported_0)) $ fun _ =>
      compareT b1.(box_Eunsupported_1) b2.(box_Eunsupported_1).

    Record box_Estmt : Set := Box_Estmt {
      box_Estmt_0 : Stmt;
      box_Estmt_1 : type
    }.
    Definition box_Estmt_compare (b1 b2 : box_Estmt) : comparison :=
      compare_lex (compareS b1.(box_Estmt_0) b2.(box_Estmt_0)) $ fun _ =>
      compareT b1.(box_Estmt_1) b2.(box_Estmt_1).

    Definition tag (e : Expr) : positive :=
      match e with
      | Eparam _ => 1
      | Eunresolved_global _ => 2
      | Eunresolved_unop _ _ => 3
      | Eunresolved_binop _ _ _ => 4
      | Eunresolved_call _ _ => 5
      | Eunresolved_member_call _ _ _ => 6
      | Eunresolved_parenlist _ _ => 7
      | Eunresolved_member _ _ => 8
      | Evar _ _ => 9
      | Eenum_const _ _ => 10
      | Eglobal _ _ => 11
      | Echar _ _ => 12
      | Estring _ _ => 13
      | Eint _ _ => 14
      | Ebool _ => 15
      | Eunop _ _ _ => 16
      | Ebinop _ _ _ _ => 17
      | Ederef _ _ => 18
      | Eaddrof _ => 19
      | Eassign _ _ _ => 20
      | Eassign_op _ _ _ _ => 21
      | Epreinc _ _ => 22
      | Epostinc _ _ => 23
      | Epredec _ _ => 24
      | Epostdec _ _ => 25
      | Eseqand _ _ => 26
      | Eseqor _ _ => 27
      | Ecomma _ _ => 28
      | Ecall _ _ => 29
      | Eexplicit_cast _ _ _ => 59
      | Ecast _ _ => 30
      | Emember _ _ _ _ _ => 31
      | Emember_ignore _ _ _ => 62
      | Emember_call _ _ _ _ => 32
      | Eoperator_call _ _ _ => 33
      | Esubscript _ _ _ => 34
      | Esizeof _ _ => 35
      | Ealignof _ _ => 36
      | Eoffsetof _ _ _ => 37
      | Econstructor _ _ _ => 38
      | Elambda _ _ => 61
      | Eimplicit _ => 39
      | Eimplicit_init _ => 40
      | Eif _ _ _ _ => 41
      | Eif2 _ _ _ _ _ _ => 42
      | Ethis _ => 43
      | Enull => 44
      | Einitlist _ _ _ => 45
      | Einitlist_union _ _ _ => 60
      | Enew _ _ _ _ _ _ => 46
      | Edelete _ _ _ _ => 47
      | Eandclean _ => 48
      | Ematerialize_temp _ _ => 49
      | Eatomic _ _ _ => 50
      | Eva_arg _ _ => 51
      | Epseudo_destructor _ _ _ => 52
      | Earrayloop_init _ _ _ _ _ _ => 53
      | Earrayloop_index _ _ => 54
      | Eopaque_ref _ _ => 55
      | Eglobal_member _ _ => 56
      | Eunsupported _ _ => 57
      | Estmt _ _ => 58
      end.
    Definition car (t : positive) : Set :=
      match t with
      | 1 => ident
      | 2 => name
      | 3 => box_Eunresolved_unop
      | 4 => box_Eunresolved_binop
      | 5 => box_Eunresolved_call
      | 6 => box_Eunresolved_member_call
      | 7 => box_Eunresolved_parenlist
      | 8 => box_Eunresolved_member
      | 9 => box_Evar
      | 10 => box_Eenum_const
      | 11 => box_Eglobal
      | 12 => box_Echar
      | 13 => box_Estring
      | 14 => box_Eint
      | 15 => bool
      | 16 => box_Eunop
      | 17 => box_Ebinop
      | 18 => box_Ederef
      | 19 => Expr
      | 20 => box_Eassign
      | 21 => box_Ebinop
      | 22 | 23 | 24 | 25 => box_Ederef
      | 26 | 27 | 28 => box_Eseqand
      | 29 => box_Ecall
      | 30 => box_Ecast
      | 31 => box_Emember
      | 32 => box_Emember_call
      | 33 => box_Eoperator_call
      | 34 => box_Eassign
      | 35 | 36 => box_Esizeof
      | 37 => box_Eoffsetof
      | 38 => box_Econstructor
      | 39 => Expr
      | 40 => type
      | 41 => box_Eif
      | 42 => box_Eif2
      | 43 => type
      | 44 => unit
      | 45 => box_Einitlist
      | 46 => box_Enew
      | 47 => box_Edelete
      | 48 => Expr
      | 49 => box_Ematerialize_temp
      | 50 => box_Eatomic
      | 51 => box_Ederef
      | 52 => box_Epseudo_destructor
      | 53 => box_Earrayloop_init
      | 54 => box_Echar
      | 55 => box_Eopaque_ref
      | 56 => box_Eglobal
      | 58 => box_Estmt
      | 59 => box_Eexplicit_cast
      | 60 => box_Einitlist_union
      | 61 => box_Elambda
      | 62 => box_Emember_ignore
      | _ => box_Eunsupported
      end.
    Definition data (e : Expr) : car (tag e) :=
      match e as e return car (tag e) with
      | Eparam X => X
      | Eunresolved_global on => on
      | Eunresolved_unop op e => Box_Eunresolved_unop op e
      | Eunresolved_binop op l r => Box_Eunresolved_binop op l r
      | Eunresolved_call on es => Box_Eunresolved_call on es
      | Eunresolved_member_call on e es => Box_Eunresolved_member_call on e es
      | Eunresolved_parenlist e es => Box_Eunresolved_parenlist e es
      | Eunresolved_member e f => Box_Eunresolved_member e f
      | Eexplicit_cast s t e => Box_Eexplicit_cast s t e
      | Evar n t => Box_Evar n t
      | Eenum_const gn id => Box_Eenum_const gn id
      | Eglobal on t => Box_Eglobal on t
      | Eglobal_member on t => Box_Eglobal on t
      | Echar c t => Box_Echar c t
      | Estring s t => Box_Estring s t
      | Eint n t => Box_Eint n t
      | Ebool b => b
      | Eunop op e t => Box_Eunop op e t
      | Ebinop op l r t => Box_Ebinop op l r t
      | Ederef e t => Box_Ederef e t
      | Eaddrof e => e
      | Eassign l r t => Box_Eassign l r t
      | Eassign_op op l r t => Box_Ebinop op l r t
      | Epreinc e t
      | Epostinc e t
      | Epredec e t
      | Epostdec e t => Box_Ederef e t
      | Eseqand l r
      | Eseqor l r
      | Ecomma l r => Box_Eseqand l r
      | Ecall e es => Box_Ecall e es
      | Ecast c e => Box_Ecast c e
      | Emember arrow e x b t => Box_Emember arrow e x b t
      | Emember_ignore arrow e n => Box_Emember_ignore arrow e n
      | Emember_call arrow m e es => Box_Emember_call arrow m e es
      | Eoperator_call oo oi es => Box_Eoperator_call oo oi es
      | Esubscript l r t => Box_Eassign l r t
      | Esizeof a t
      | Ealignof a t => Box_Esizeof a t
      | Eoffsetof cls m t => Box_Eoffsetof cls m t
      | Econstructor cls es t => Box_Econstructor cls es t
      | Elambda n es => Box_Elambda n es
      | Eimplicit e => e
      | Eimplicit_init t => t
      | Eif c l r t => Box_Eif c l r t
      | Eif2 n s c l r t => Box_Eif2 n s c l r t
      | Ethis t => t
      | Enull => ()
      | Einitlist es i t => Box_Einitlist es i t
      | Einitlist_union es i t => Box_Einitlist_union es i t
      | Enew fn es a ty sz i => Box_Enew fn es a ty sz i
      | Edelete a fn e t => Box_Edelete a fn e t
      | Eandclean e => e
      | Ematerialize_temp e vc => Box_Ematerialize_temp e vc
      | Eatomic op es t => Box_Eatomic op es t
      | Estmt s t => Box_Estmt s t
      | Eva_arg e t => Box_Ederef e t
      | Epseudo_destructor a t e => Box_Epseudo_destructor a t e
      | Earrayloop_init on s lev len i t => Box_Earrayloop_init on s lev len i t
      | Earrayloop_index c t => Box_Echar c t
      | Eopaque_ref n t => Box_Eopaque_ref n t
      | Eunsupported msg t => Box_Eunsupported msg t
      end.
    Definition compare_data (t : positive) : car t -> car t -> comparison :=
      match t as t return car t -> car t -> comparison with
      | 1 => PrimString.compare
      | 2 => compareN
      | 3 => box_Eunresolved_unop_compare
      | 4 => box_Eunresolved_binop_compare
      | 5 => box_Eunresolved_call_compare
      | 6 => box_Eunresolved_member_call_compare
      | 7 => box_Eunresolved_parenlist_compare
      | 8 => box_Eunresolved_member_compare
      | 9 => box_Evar_compare
      | 10 => box_Eenum_const_compare
      | 11 => box_Eglobal_compare
      | 12 => box_Echar_compare
      | 13 => box_Estring_compare
      | 14 => box_Eint_compare
      | 15 => Bool.compare
      | 16 => box_Eunop_compare
      | 17 => box_Ebinop_compare
      | 18 => box_Ederef_compare
      | 19 => compareE
      | 20 => box_Eassign_compare
      | 21 => box_Ebinop_compare
      | 22 | 23 | 24 | 25 => box_Ederef_compare
      | 26 | 27 | 28 => box_Eseqand_compare
      | 29 => box_Ecall_compare
      | 30 => box_Ecast_compare
      | 31 => box_Emember_compare
      | 32 => box_Emember_call_compare
      | 33 => box_Eoperator_call_compare
      | 34 => box_Eassign_compare
      | 35 | 36 => box_Esizeof_compare
      | 37 => box_Eoffsetof_compare
      | 38 => box_Econstructor_compare
      | 39 => compareE
      | 40 => compareT
      | 41 => box_Eif_compare
      | 42 => box_Eif2_compare
      | 43 => compareT
      | 44 => fun _ _ => Eq
      | 45 => box_Einitlist_compare
      | 46 => box_Enew_compare
      | 47 => box_Edelete_compare
      | 48 => compareE
      | 49 => box_Ematerialize_temp_compare
      | 50 => box_Eatomic_compare
      | 51 => box_Ederef_compare
      | 52 => box_Epseudo_destructor_compare
      | 53 => box_Earrayloop_init_compare
      | 54 => box_Echar_compare
      | 55 => box_Eopaque_ref_compare
      | 56 => box_Eglobal_compare
      | 58 => box_Estmt_compare
      | 59 => box_Eexplicit_cast_compare
      | 60 => box_Einitlist_union_compare
      | 61 => box_Elambda_compare
      | 62 => box_Emember_ignore_compare
      | _ => box_Eunsupported_compare
      end.

    #[local] Notation compare_ctor := (compare_ctor tag car data compare_data).
    #[local] Notation compare_tag := (compare_tag tag).

    #[local] Notation COMP e := (compare_ctor (Reduce (tag e)) (fun _ => Reduce (data e))) (only parsing).

    Definition compare_body (e : Expr) : Expr -> comparison :=
      match e with
      | Eparam X => COMP (Eparam X : Expr)
      | Eunresolved_global on => COMP (Eunresolved_global on)
      | Eunresolved_unop op e => COMP (Eunresolved_unop op e)
      | Eunresolved_binop op l r => COMP (Eunresolved_binop op l r)

      | Eunresolved_call on es => COMP (Eunresolved_call on es)
      | Eunresolved_member_call on e es => COMP (Eunresolved_member_call on e es)
      | Eunresolved_parenlist e es => COMP (Eunresolved_parenlist e es)
      | Eunresolved_member e f => COMP (Eunresolved_member e f)
      | Eexplicit_cast s e t => COMP (Eexplicit_cast s e t)

      | Evar n t => COMP (Evar n t)

      | Eenum_const gn id => COMP (Eenum_const gn id)
      | Eglobal on t => COMP (Eglobal on t)
      | Eglobal_member on t => COMP (Eglobal_member on t)

      | Echar c t => COMP (Echar c t)
      | Estring s t => COMP (Estring s t)
      | Eint n t => COMP (Eint n t)

      | Ebool b => COMP (Ebool b : Expr)
      | Eunop op e t => COMP (Eunop op e t)
      | Ebinop op l r t => COMP (Ebinop op l r t)
      | Ederef e t => COMP (Ederef e t)
      | Eaddrof e => COMP (Eaddrof e)

      | Eassign l r t => COMP (Eassign l r t)
      | Eassign_op op l r t => COMP (Eassign_op op l r t)
      | Epreinc e t => COMP (Epreinc e t)
      | Epostinc e t => COMP (Epostinc e t)
      | Epredec e t => COMP (Epredec e t)

      | Epostdec e t => COMP (Epostdec e t)
      | Eseqand l r => COMP (Eseqand l r)
      | Eseqor l r => COMP (Eseqor l r)
      | Ecomma l r => COMP (Ecomma l r)
      | Ecall e es => COMP (Ecall e es)

      | Ecast c e => COMP (Ecast c e)
      | Emember arr e x b t => COMP (Emember arr e x b t)
      | Emember_ignore arr e n => COMP (Emember_ignore arr e n)
      | Emember_call arr m e es => COMP (Emember_call arr m e es)
      | Eoperator_call oo oi es => COMP (Eoperator_call oo oi es)
      | Esubscript l r t => COMP (Esubscript l r t)

      | Esizeof a t => COMP (Esizeof a t)
      | Ealignof a t => COMP (Ealignof a t)
      | Eoffsetof cls m t => COMP (Eoffsetof cls m t)
      | Econstructor cls es t => COMP (Econstructor cls es t)
      | Elambda n es => COMP (Elambda n es)

      | Eimplicit e => COMP (Eimplicit e)

      | Eimplicit_init t => COMP (Eimplicit_init t)
      | Eif c l r t => COMP (Eif c l r t)
      | Eif2 n s c l r t => COMP (Eif2 n s c l r t)
      | Ethis t => COMP (Ethis t)
      | Enull => compare_tag (Reduce (tag Enull))

      | Einitlist es i t => COMP (Einitlist es i t)
      | Einitlist_union es i t => COMP (Einitlist_union es i t)

      | Enew fn es a ty sz i => COMP (Enew fn es a ty sz i)
      | Edelete a fn e t => COMP (Edelete a fn e t)
      | Eandclean e => COMP (Eandclean e)
      | Ematerialize_temp e vc => COMP (Ematerialize_temp e vc)

      | Eatomic op es t => COMP (Eatomic op es t)
      | Eva_arg e t => COMP (Eva_arg e t)
      | Epseudo_destructor a t e => COMP (Epseudo_destructor a t e)
      | Earrayloop_init on s lev len i t => COMP (Earrayloop_init on s lev len i t)
      | Earrayloop_index c t => COMP (Earrayloop_index c t)

      | Eopaque_ref n t => COMP (Eopaque_ref n t)
      | Eunsupported msg t => COMP (Eunsupported msg t)
      | Estmt s t => compare_ctor (Reduce (tag $ Estmt s t)) (fun _ => Reduce (data $ Estmt s t))
      end.
  End compare_body.
End Expr.

Module VarDecl.
  Section compare_body.
    Context (compareN : name -> name -> comparison).
    Context (compareT : type -> type -> comparison).
    Context (compareE : Expr -> Expr -> comparison).
    Context (compareBD : BindingDecl -> BindingDecl -> comparison).
    Context (compareS : Stmt -> Stmt -> comparison).

    #[local] Canonical name_comparator :=
      {| _car := name
      ; _compare := compareN |}.
    #[local] Canonical type_comparator :=
      {| _car := type
       ; _compare := compareT |}.
    #[local] Canonical expr_comparator :=
      {| _car := Expr
      ; _compare := compareE |}.
    #[local] Canonical VarDecl_comparator :=
      {| _car := BindingDecl
      ; _compare := compareBD |}.

    Definition tag (vd : VarDecl) : positive :=
      match vd with
      | Dvar _ _ _ => 1
      | Ddecompose _ _ _ => 2
      | Dinit _ _ _ _ => 3
      end.
    Definition car (vd : positive) : Set :=
      match vd return Set with
      | 1 => localname * type * option Expr
      | 2 => Expr * ident * list BindingDecl
      | _ => bool * name * type * option Expr
      end%type.
    Definition data (vd : VarDecl) : car (tag vd) :=
      match vd with
      | Dvar a b c => (a, b, c)
      | Ddecompose a b c => (a, b, c)
      | Dinit a b c d => (a, b, c, d)
      end.
    Definition compare_data (k : positive) : car k -> car k -> comparison :=
      match k as k return car k -> car k -> comparison with
      | 1 => _compare
      | 2 => _compare
      | _ => _compare
      end.

    #[local] Notation compare_ctor X := (compare_ctor tag car data compare_data (Reduce (tag X)) (fun _ => Reduce (data X))) (only parsing).
    Definition compare_body (vd : VarDecl) : VarDecl -> comparison :=
      match vd with
      | Dvar a b c => compare_ctor (Dvar a b c)
      | Ddecompose a b c => compare_ctor (Ddecompose a b c)
      | Dinit a b c d => compare_ctor (Dinit a b c d)
      end.
  End compare_body.
End VarDecl.

Module BindingDecl.
  Section compare_body.
    Context (compareT : type -> type -> comparison).
    Context (compareE : Expr -> Expr -> comparison).
    Context (compareVD : VarDecl -> VarDecl -> comparison).

    #[local] Canonical type_comparator :=
      {| _car := type
       ; _compare := compareT |}.
    #[local] Canonical expr_comparator :=
      {| _car := Expr
      ; _compare := compareE |}.
    #[local] Canonical VarDecl_comparator :=
      {| _car := VarDecl
      ; _compare := compareVD |}.

    Definition tag (vd : BindingDecl) : positive :=
      match vd with
      | Bvar _ _ _ => 1
      | Bbind _ _ _ => 2
      end.
    Definition car (vd : positive) : Set :=
      localname * type * Expr.
    Definition data (vd : BindingDecl) : car (tag vd) :=
      match vd with
      | Bvar a b c => (a, b, c)
      | Bbind a b c => (a, b, c)
      end.
    Definition compare_data (k : positive) : car k -> car k -> comparison :=
      _compare.

    #[local] Notation compare_ctor X := (compare_ctor tag car data compare_data (Reduce (tag X)) (fun _ => Reduce (data X))) (only parsing).
    Definition compare_body (vd : BindingDecl) : BindingDecl -> comparison :=
      match vd with
      | Bvar a b c => compare_ctor (Bvar a b c)
      | Bbind a b c => compare_ctor (Bbind a b c)
      end.
  End compare_body.
End BindingDecl.


Module Stmt.
  Section compare_body.
    Context (compareN : name -> name -> comparison).
    Context (compareT : type -> type -> comparison).
    Context (compareE : Expr -> Expr -> comparison).
    Context (compareVD : VarDecl -> VarDecl -> comparison).
    Context (compareS : Stmt -> Stmt -> comparison).

    #[local] Canonical name_comparator :=
      {| _car := name
      ; _compare := compareN |}.
    #[local] Canonical type_comparator :=
      {| _car := type
       ; _compare := compareT |}.
    #[local] Canonical expr_comparator :=
      {| _car := Expr
      ; _compare := compareE |}.
    #[local] Canonical VarDecl_comparator :=
      {| _car := VarDecl
      ; _compare := compareVD |}.
    #[local] Canonical Stmt_comparator :=
      {| _car := _
      ; _compare := compareS |}.

    Definition tag (s : Stmt) : positive :=
      match s with
      | Sseq _ => 1
      | Sdecl _ => 2
      | Sif _ _ _ _ => 3
      | Sif_consteval _ _ => 19
      | Swhile _ _ _ => 4
      | Sfor _ _ _ _ => 5
      | Sdo _ _ => 6
      | Sswitch _ _ _ => 7
      | Scase _ => 8
      | Sdefault => 9
      | Sbreak => 10
      | Scontinue => 11
      | Sreturn _ => 12
      | Sexpr _ => 13
      | Sattr _ _ => 14
      | Sasm _ _ _ _ _ => 15
      | Slabeled _ _ => 16
      | Sgoto _ => 17
      | Sunsupported _ => 18
      end.
    Definition car (k : positive) : Set :=
      match k with
      | 1 => list Stmt
      | 2 => list VarDecl
      | 3 => option VarDecl * Expr * Stmt * Stmt
      | 19 => Stmt * Stmt
      | 4 => option VarDecl * Expr * Stmt
      | 5 => option Stmt * option Expr * option Expr * Stmt
      | 6 => Stmt * Expr
      | 7 => option VarDecl * Expr * Stmt
      | 8 => SwitchBranch
      | 9 => unit
      | 10 => unit
      | 11 => unit
      | 12 => option Expr
      | 13 => Expr
      | 14 => list ident * Stmt
      | 15 => PrimString.string * bool * list (ident * Expr) * list (ident * Expr) * list ident
      | 16 => ident * Stmt
      | 17 => ident
      | _ => PrimString.string
      end.
    Definition data (s : Stmt) : car (tag s) :=
      match s with
      | Sseq a => a
      | Sdecl a => a
      | Sif a b c d => (a,b,c,d)
      | Sif_consteval a b => (a,b)
      | Swhile a b c => (a,b,c)
      | Sfor a b c d => (a,b,c,d)
      | Sdo a b => (a,b)
      | Sswitch a b c => (a,b,c)
      | Scase a => a
      | Sdefault => tt
      | Sbreak => ()
      | Scontinue => ()
      | Sreturn a => a
      | Sexpr a => a
      | Sattr a b => (a,b)
      | Sasm a b c d e => (a,b,c,d,e)
      | Slabeled a b => (a,b)
      | Sgoto a => a
      | Sunsupported a => a
      end.

    Definition compare_data  (k : positive) : car k -> car k -> comparison :=
      match k as k return car k -> car k -> comparison with
      | 1 => _compare
      | 2 => _compare
      | 3 => _compare
      | 4 => _compare
      | 5 => _compare
      | 6 => _compare
      | 7 => _compare
      | 8 => _compare
      | 9 => _compare
      | 10 => _compare
      | 11 => _compare
      | 12 => _compare
      | 13 => _compare
      | 14 => _compare
      | 15 => _compare
      | 16 => _compare
      | 17 => _compare
      | 19 => _compare
      | _ => _compare
      end.

    #[local] Notation compare_ctor X := (compare_ctor tag car data compare_data (Reduce (tag X)) (fun _ => Reduce (data X))) (only parsing).
    Definition compare_body (s : Stmt) : Stmt -> comparison :=
      match s with
      | Sseq a => compare_ctor (Sseq a)
      | Sdecl a => compare_ctor (Sdecl a)
      | Sif a b c d => compare_ctor (Sif a b c d)
      | Sif_consteval a b => compare_ctor (Sif_consteval a b)
      | Swhile a b c => compare_ctor (Swhile a b c)
      | Sfor a b c d => compare_ctor (Sfor a b c d)
      | Sdo a b => compare_ctor (Sdo a b)
      | Sswitch a b c => compare_ctor (Sswitch a b c)
      | Scase a => compare_ctor (Scase a)
      | Sdefault => compare_ctor (Sdefault)
      | Sbreak => compare_ctor (Sbreak)
      | Scontinue => compare_ctor (Scontinue)
      | Sreturn a => compare_ctor (Sreturn a)
      | Sexpr a => compare_ctor (Sexpr a)
      | Sattr a b => compare_ctor (Sattr a b)
      | Sasm a b c d e => compare_ctor (Sasm a b c d e)
      | Slabeled a b => compare_ctor (Slabeled a b)
      | Sgoto a => compare_ctor (Sgoto a)
      | Sunsupported a => compare_ctor (Sunsupported a)
      end.

  End compare_body.
End Stmt.

(* This is needed to speed up compilation on the guardedness check on the
   following [compare{N,T,E,VD,S}] functions. Without this, the termination
   checker *does succeed* but it takes ~800s.
 *)
#[local] Unset Guard Checking.

Section compare.


  (* NOTE: Do not remove the {struct} annotations here. They may seem trivial
     but they are vital for performance (<1s instead of 40s). *)

  Fixpoint compareN (n : name) {struct n} : name -> comparison :=
    name.compare_body compareN compareT compareE n

  with compareT (t : type) {struct t} : type -> comparison :=
    type.compare_body compareN compareT compareE t

  with compareE (e : Expr) {struct e} : Expr -> comparison :=
    Expr.compare_body compareN compareT compareC compareE compareS e

  with compareVD (vd : VarDecl) {struct vd} : VarDecl -> comparison :=
    VarDecl.compare_body compareN compareT compareE compareBD vd

  with compareBD (bd : BindingDecl) {struct bd} : BindingDecl -> comparison :=
    BindingDecl.compare_body compareT compareE bd

  with compareS (s : Stmt) {struct s} : Stmt -> comparison :=
    Stmt.compare_body compareE compareVD compareS s

  with compareC (s : Cast) {struct s} : Cast -> comparison :=
    Cast.compare_body compareT s
  .

End compare.

#[local] Set Guard Checking.

Section compare_instances.

  #[global] Instance name_compare : Compare name := compareN.
  #[global] Instance type_compare : Compare type := compareT.
  #[global] Instance Expr_compare : Compare Expr := compareE.
  #[global] Instance VarDecl_compare : Compare VarDecl := compareVD.
  #[global] Instance Stmt_compare : Compare Stmt := compareS.

End compare_instances.

(** ** Name maps *)

#[global] Declare Instance name_comparison :
  Comparison (compareN).	(* TODO *)
#[global] Declare Instance type_comparison :
  Comparison (compareT). (* TODO *)
#[global] Declare Instance Expr_comparison :
  Comparison (compareE). (* TODO *)
#[global] Declare Instance VarDecl_comparison :
  Comparison (compareVD). (* TODO *)
#[global] Declare Instance Stmt_comparison :
  Comparison (compareS). (* TODO *)
#[global] Declare Instance temp_arg_comparison :
  Comparison (temp_arg.compare (compareN) (compareT) (compareE)). (* TODO *)

#[global] Declare Instance name_leibniz_comparison :
  LeibnizComparison (compareN).	(* TODO *)
#[global] Declare Instance type_leibniz_comparison :
  LeibnizComparison (compareT). (* TODO *)
#[global] Declare Instance Expr_leibniz_comparison :
  LeibnizComparison (compareE). (* TODO *)
#[global] Declare Instance VarDecl_leibniz_comparison :
  LeibnizComparison (compareVD). (* TODO *)
#[global] Declare Instance Stmt_leibniz_comparison :
  LeibnizComparison (compareS). (* TODO *)
#[global] Declare Instance temp_arg_leibniz_comparison :
  LeibnizComparison (temp_arg.compare (compareN) (compareT) (compareE)). (* TODO *)


#[global] Instance name_eq_dec : EqDecision name :=
  LeibnizComparison.from_comparison.
#[global] Instance type_eq_dec : EqDecision type :=
  LeibnizComparison.from_comparison.
#[global] Instance Expr_eq_dec : EqDecision Expr :=
  LeibnizComparison.from_comparison.
#[global] Instance VarDecl_eq_dec : EqDecision VarDecl :=
  LeibnizComparison.from_comparison.
#[global] Instance Stmt_eq_dec : EqDecision Stmt :=
  LeibnizComparison.from_comparison.
#[global] Instance temp_arg_eq_dec : EqDecision temp_arg :=
  LeibnizComparison.from_comparison.
