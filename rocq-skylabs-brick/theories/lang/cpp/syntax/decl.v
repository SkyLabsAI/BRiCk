(*
 * Copyright (c) 2020-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.prelude.base.
Require Import bluerock.prelude.compare.
Require Import bluerock.lang.cpp.syntax.core.
Require Import bluerock.lang.cpp.syntax.types.
Require Import bluerock.lang.cpp.syntax.stmt.

#[local] Notation EqDecision1 T := (∀ (A : Set), EqDecision A -> EqDecision (T A)) (only parsing).
#[local] Notation EqDecision2 T := (∀ (A : Set), EqDecision A -> EqDecision1 (T A)) (only parsing).
#[local] Notation EqDecision3 T := (∀ (A : Set), EqDecision A -> EqDecision2 (T A)) (only parsing).
#[local] Notation EqDecision4 T := (∀ (A : Set), EqDecision A -> EqDecision3 (T A)) (only parsing).
#[local] Tactic Notation "solve_decision" := intros; solve_decision.

Variant OrDefault {t : Set} : Set :=
  | Defaulted
  | UserDefined (_ : t).
Arguments OrDefault : clear implicits.
#[global] Instance OrDefault_inh: forall {T: Set}, Inhabited (OrDefault T).
Proof. repeat constructor. Qed.
#[global] Instance OrDefault_eq_dec: forall {T: Set}, EqDecision T -> EqDecision (OrDefault T).
Proof. solve_decision. Defined.

Module OrDefault.
  Import UPoly.

  Definition fmap {A B : Set} (f : A -> B) (v : OrDefault A) : OrDefault B :=
    match v with
    | Defaulted => Defaulted
    | UserDefined a => UserDefined (f a)
    end.
  #[global] Arguments fmap _ _ _ & _ : assert.

  (*
  #[universes(polymorphic)]
  Definition traverse@{u | } {F : Set -> Type@{u}} `{!FMap F, !MRet F, AP : !Ap F}
    {A B : Set} (f : A -> F B) (v : OrDefault A) : F (OrDefault B) :=
    match v with
    | Defaulted => mret Defaulted
    | UserDefined a => UserDefined <$> f a
    end.
  #[global] Arguments traverse _ _ _ _ _ _ & _ _ : assert.
  #[global] Hint Opaque traverse : typeclass_instances.
  *)

  #[global,universes(polymorphic)]
  Instance OrDefault_traverse : Traverse OrDefault :=
    fun F _ _ _ _ _ f od =>
      match od with
      | Defaulted => mret Defaulted
      | UserDefined v => UserDefined <$> f v
      end.
End OrDefault.

(** ** Type Declarations *)

(** Record an offset in _bits_. *)
Record LayoutInfo : Set :=
{ li_offset : Z }.
#[global] Instance: EqDecision LayoutInfo.
Proof. solve_decision. Defined.

Record Member' : Set := mkMember
{ mem_name : field_name.t
; mem_type : type
; mem_mutable : bool
; mem_init : option Expr
; mem_layout : LayoutInfo }.
Notation Member := Member'.
#[global] Arguments mkMember _ _ _ _ _ : assert.
#[global] Instance Member_eq_dec : EqDecision Member.
Proof. solve_decision. Defined.

Record Union' : Set := Build_Union
{ u_fields : list Member
  (* ^ fields with type, initializer, and layout information *)
; u_dtor : obj_name
  (* ^ the name of the destructor *)
; u_trivially_destructible : bool
  (* ^ whether objects of the union type are trivially destructible. *)
; u_delete : option obj_name
  (* ^ name of [operator delete], if it exists.
     See [s_delete] for more information. *)
; u_size : N
  (* ^ size of the union (including padding) *)
; u_alignment : N
  (* ^ alignment of the union *)
}.
Notation Union := Union'.
#[global] Arguments Build_Union _ _ _ _ _ _ : assert.
#[global] Instance Union'_eq_dec : EqDecision Union.
Proof. solve_decision. Defined.

Variant LayoutType : Set := POD | Standard | Unspecified.
#[global] Instance: EqDecision LayoutType.
Proof. solve_decision. Defined.

Record Struct' : Set := Build_Struct
{ s_bases : list (classname * LayoutInfo)
  (* ^ base classes *)
; s_fields : list Member
  (* ^ fields with type, initializer, and layout information *)
; s_virtuals : list (obj_name * option obj_name)
  (* ^ function_name -> symbol *)
; s_overrides : list (obj_name * obj_name)
  (* ^ k |-> v ~ update k with v *)
; s_dtor : obj_name
  (* ^ the name of the destructor.
     NOTE at the C++ abstract machine level, there is only
          one destructor, but implementations (and name mangling)
          use multiple destructors in cases of classes with [virtual]
          inheritence.
   *)
; s_trivially_destructible : bool
  (* ^ this is actually computable, and we could compute it *)
; s_delete : option obj_name
  (* ^ the name of an class-specific <<operator delete>> that is used to delete
     the object. Note, we do not need an <<operator delete[]>> because these
     are statically resolved at the call site <<delete[]>> does not involve
     <<virtual>> dispatch. *)
; s_layout : LayoutType
  (* ^ the type of layout semantics *)
(* The remaining fields are implementation-dependent. They might be mandated by the per-platform ABI. *)
; s_size : N
  (* ^ size of the structure (including padding) *)
; s_alignment : N
  (* ^ alignment of the structure *)
}.
Notation Struct := Struct'.
#[global] Arguments Build_Struct _ _ _ _ _ _ _ _ _ _ : assert.
#[global] Instance Struct_eq_dec : EqDecision Struct.
Proof. solve_decision. Defined.

(** [has_vtable s] determines whether [s] has any <<virtual>> methods
    (or bases). Having a vtable is *not* a transitive property.
    A class that only inherits <<virtual>> methods does not have a
    vtable.

    Note that methods that override virtual methods are implicitly virtual.
    This includes destructor.
 *)
Definition has_vtable (s : Struct) : bool :=
  match s.(s_virtuals) with
  | nil => false
  | _ :: _ => true
  end.
#[global] Arguments has_vtable _ : assert.

(* [has_virtual_dtor s] returns true if the destructor is virtual. *)
Definition has_virtual_dtor (s : Struct) : bool :=
  List.existsb (fun '(a,_) => bool_decide (a = s.(s_dtor))) s.(s_virtuals).
#[global] Arguments has_virtual_dtor _ : assert.

Variant Ctor_type : Set := Ct_Complete | Ct_Base | Ct_alloc | Ct_Comdat.
#[global] Instance: EqDecision Ctor_type.
Proof. solve_decision. Defined.

(** ** Value Declarations *)

Module exception_spec.
  (**
  C++11 exception specifications for functions.

  This type is equivalent to <<option(NoThrow | MayThrow)>>, but flattened into a single
  variant for performance. The <<option>> is necessary because information is not always
  available, e.g. for templated functions with <<noexcept>> specifications depending on
  template parameters.

  Functions marked as [NoThrow] can throw exceptions internally, but those
  exceptions are not propagated to callers in the usual way.
  - Starting with C++17, throwing an exception from a [NoThrow] function is
    guaranteed to call <<std::terminate>> and terminate program execution.
    And in this scenario, unwinding the stack and calling destructors is optional.
  - Before C++17, the language also included dynamic exception specifications,
    with more complex behavior
    (see <https://en.cppreference.com/w/cpp/language/except_spec.html>).

  Currently, BRiCK does _not_ support exceptions, so semantics for
  the different scenarios are not defined yet.

  For now, BRiCk only uses this to infer whether a <<new()>> operator overload signals
  allocation failure by throwing exceptions ([MayThrow] case), or returning
  <<nullptr>> ([NoThrow] case).
  *)
  Variant t : Set :=
    | Unknown (** Unknown exception spec. *)
    | NoThrow (** Not supposed to throw exceptions *)
    | MayThrow (** Allowed to throw exceptions. *).

  #[global] Instance: SubsetEq t :=
    fun a b => a = Unknown \/ a = b.
  #[global] Instance: RelDecision (⊆@{t}).
  Proof. intros [ | | ]  [ | | ]; compute; intuition congruence. Defined.
  #[global] Instance: Reflexive (⊆@{t}).
  Proof. intros [ | | ]; compute; intuition congruence. Qed.
  #[global] Instance: Transitive (⊆@{t}).
  Proof. intros [ | | ] [ | | ] [ | | ]; compute; intuition congruence. Qed.

  Import PrimInt63.
  Definition prim_tag (r : exception_spec.t) : PrimInt63.int :=
    match r with
    | exception_spec.Unknown => 0
    | exception_spec.NoThrow => 1
    | exception_spec.MayThrow => 2
    end%uint63.

  Definition compare (x y : exception_spec.t) : comparison :=
    PrimInt63.compare (prim_tag x) (prim_tag y).

  #[global] Instance: Comparison compare.
  Proof. apply by_prim_tag_comparison. Qed.
  #[global] Instance: LeibnizComparison compare.
  Proof. intros [ | | ] [ | | ]; compute; done. Qed.
  #[global] Instance: EqDecision t := LeibnizComparison.from_comparison.
End exception_spec.

(** *** Functions *)
Variant FunctionBody' : Set :=
| Impl (_ : Stmt)
| Builtin (_ : BuiltinFn)
.
Notation FunctionBody := FunctionBody'.
#[global] Instance: EqDecision FunctionBody.
Proof. solve_decision. Defined.

Record Func' : Set := Build_Func
{ f_return : type
; f_params : list (ident * type)
; f_cc     : calling_conv
; f_arity  : function_arity
; f_exception : exception_spec.t
; f_body   : option FunctionBody
}.
Notation Func := Func'.
#[global] Arguments Build_Func _ _ _ _ _ _ : assert.
#[global] Instance: EqDecision Func.
Proof. solve_decision. Defined.
#[global] Instance Func_inhabited : Inhabited Func.
Proof. solve_inhabited. Qed.

(** *** Methods *)
Record Method' : Set := Build_Method
{ m_return  : type
; m_class   : classname
; m_this_qual : type_qualifiers
; m_params  : list (ident * type)
; m_cc      : calling_conv
; m_arity   : function_arity
; m_exception : exception_spec.t
; m_body    : option (OrDefault Stmt)
}.
Notation Method := Method'.
#[global] Arguments Build_Method _ _ _ _ _ _ _ _ : assert.
#[global] Instance: EqDecision Method.
Proof. solve_decision. Defined.

Definition static_method (m : Method)
  : Func :=
  {| f_return := m.(m_return)
   ; f_params := m.(m_params)
   ; f_cc := m.(m_cc)
   ; f_arity := m.(m_arity)
   ; f_exception := m.(m_exception)
   ; f_body := match m.(m_body) with
               | Some (UserDefined body) => Some (Impl body)
               | _ => None
               end |}.

(** *** Constructors *)

Variant InitPath' : Set :=
| InitBase (_ : classname)
| InitField (_ : field_name.t)
| InitIndirect (anon_path : list (field_name.t * classname)) (_ : field_name.t)
| InitThis.
#[global] Notation InitPath := InitPath'.
#[global] Instance: EqDecision InitPath.
Proof. solve_decision. Defined.

Record Initializer' : Set := Build_Initializer
  { init_path : InitPath
  ; init_init : Expr }.
Notation Initializer := Initializer'.
#[global] Arguments Build_Initializer _ _ : assert.
#[global] Instance: EqDecision Initializer.
Proof. solve_decision. Defined.

Record Ctor' : Set := Build_Ctor
{ c_class  : classname
; c_params : list (ident * type)
; c_cc     : calling_conv
; c_arity  : function_arity
; c_exception : exception_spec.t
; c_body   : option (OrDefault (list Initializer * Stmt))
}.
Notation Ctor := Ctor'.
#[global] Arguments Build_Ctor _ _ _ _ _ _ : assert.
#[global] Instance: EqDecision Ctor.
Proof. solve_decision. Defined.

(** *** Destructors *)

Record Dtor' : Set := Build_Dtor
{ d_class  : classname
; d_cc     : calling_conv
; d_exception : exception_spec.t
; d_body   : option (OrDefault Stmt)
}.
Notation Dtor := Dtor'.
#[global] Arguments Build_Dtor _ _ _ _ : assert.
#[global] Instance: EqDecision Dtor.
Proof. solve_decision. Defined.

Variant Dtor_type : Set := Dt_Deleting | Dt_Complete | Dt_Base | Dt_Comdat.
#[global] Instance: EqDecision Dtor_type.
Proof. solve_decision. Defined.
