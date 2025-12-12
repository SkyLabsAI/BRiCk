(*
 * Copyright (c) 2023-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.prelude.lens.
Require Import bluerock.lang.cpp.syntax.prelude.
Require Import bluerock.lang.cpp.syntax.core.
Import UPoly.

#[local] Set Primitive Projections.
#[local] Set Printing Implicit.

#[local] Set Universe Polymorphism.
#[local] Set Polymorphic Inductive Cumulativity.
#[local] Unset Auto Template Polymorphism.
#[local] Unset Universe Minimization ToSet.

(** * Handlers for simple AST traversals *)
(**
Types of "handlers" for interesting constructors of [type], [Expr].

These types support the generic traversals in mtraverse2.v. Clients of
_those_ dictate the sets of "interesting constructors".

The handler for a constructor receives the constructor's arguments as
well as (delayed) traversal results.
*)

Record type_handler'@{u} {N T E : Type@{u}} : Type@{u} := {
  (** Dependent types *)
  handle_Tparam (_ : ident) : T;
  handle_Tresult_param (_ : ident) : T;
  handle_Tresult_global (_ : name) (_ : unit -> N) : T;
  handle_Tresult_unop (_ : RUnOp) (_ : decltype)
    (_ : unit -> T) : T;
  handle_Tresult_binop (_ : RBinOp) (_ _ : decltype)
    (_ _ : unit -> T) : T;
  handle_Tresult_call (_ : name) (_ : list decltype)
    (_ : unit -> N) (_ : unit -> list T) : T;
  handle_Tresult_member_call (_ : name) (_ : decltype) (_ : list decltype)
    (_ : unit -> N) (_ : unit -> T) (_ : unit -> list T) : T;
  handle_Tresult_parenlist (_ : decltype) (_ : list decltype)
    (_ : unit -> T) (_ : unit -> list T) : T;
  handle_Tresult_member (_ : decltype) (_ : name) (_ : unit -> T) (_ : unit -> N) : T;
  (** Alias expansion *)
  handle_Tnamed (_ : name) (_ : unit -> N) : T;
  (** Reference collapsing *)
  handle_Tref (_ : type) (_ : unit -> T) : T;
  handle_Trv_ref (_ : type) (_ : unit -> T) : T;
  handle_Tqualified (_ : type_qualifiers) (_ : type) (_ : unit -> T) : T;
}.
Arguments type_handler' : clear implicits.
Notation type_handler M := (
  type_handler'
    (M name)
    (M decltype)
    (M Expr)
).

Record expr_handler'@{u} {N T E : Set} {F : Set -> Type@{u}} : Type@{u} := {
  (** Dependent terms *)
  handle_Eparam (_ : ident) : F E;
  handle_Eunresolved_global (_ : name) (_ : unit -> F N) : F E;
  handle_Eunresolved_unop (_ : RUnOp) (_ : Expr) (_ : unit -> F E) : F E;
  handle_Eunresolved_binop (_ : RBinOp) (_ _ : Expr) (_ _ : unit -> F E) : F E;
  handle_Eunresolved_call (_ : name) (_ : list Expr)
    (_ : unit -> F N) (_ : unit -> list (F E)) : F E;
  handle_Eunresolved_member_call (_ : name) (_ : Expr) (_ : list Expr)
    (_ : unit -> F N) (_ : unit -> F E) (_ : unit -> list (F E)) : F E;
  handle_Eunresolved_parenlist (_ : option type) (_ : list Expr)
    (_ : unit -> option (F T)) (_ : unit -> list (F E)) : F E;
  handle_Eunresolved_member (_ : Expr) (_ : name) (_ : unit -> F E) (_ : unit -> F N) : F E;
  (** Embedded expression types *)
  handle_expr_type : F T -> F T;
  (** casts *)
  handle_Eunresolved_cast (_ : type) (_ : unit -> F T) (_ : Expr) (_ : unit -> F E) : F E;

  handle_unresolved_init (_ : type) (_ : unit -> F T) (_ : option (Expr * (unit -> F E))) : F (T * option E)%type
}.
Arguments expr_handler' : clear implicits.
Notation expr_handler M := (
  expr_handler'
    name
    type
    Expr M
).

(**
Handlers for derived traversal functions (e.g., for a traversal of
type <<MMethod -> M SMethod>>) are a bit different from the preceding
handlers as they aren't involved in the mutually recursive traversals
on names, types, and expressions.
*)

Record core_traversal@{u} {F : Set -> Type@{u}} : Type@{u} :=
{ (** Traversal functions *)
  handle_traverseN (_ : name) : F name;
  handle_traverseT (_ : type) : F type;
  handle_traverseE (_ : Expr) : F Expr;
  handle_traverseS (_ : Stmt) : F Stmt;
  (** Initializers *)
  handle_classname (_ : classname) : F classname;
  handle_traverseE_init (_ : type) (_ : option Expr) : F (type * option Expr)%type;
}.
Arguments core_traversal : clear implicits.

(** ** Basic handlers *)

Section handlers.
  Universe u.
  Context {F : Set -> Type@{u}} `{!FMap F, !MRet F, AP : !Ap F}.

  (** Just traverse *)
  Definition handle_type_traverse : type_handler F := {|
    handle_Tparam T := mret $ Tparam T;
    handle_Tresult_param X := mret $ Tresult_param X;
    handle_Tresult_global _ n := Tresult_global <$> n ();
    handle_Tresult_unop o _ e := Tresult_unop o <$> e ();
    handle_Tresult_binop o _ _ l r := Tresult_binop o <$> l () <*> r ();
    handle_Tresult_call _ _ n ts := Tresult_call <$> n () <*> sequence@{eta list} (ts ());
    handle_Tresult_member_call _ _ _ n t ts := Tresult_member_call <$> n () <*> t () <*> sequence@{eta list} (ts ());
    handle_Tresult_parenlist _ _ t ts := Tresult_parenlist <$> t () <*> sequence@{eta list} (ts ());
    handle_Tresult_member _ _ t n := Tresult_member <$> t () <*> n ();
    handle_Tnamed _ n := Tnamed <$> n ();
    handle_Tref _ t := Tref <$> t ();
    handle_Trv_ref _ t := Trv_ref <$> t ();
    handle_Tqualified cv _ t := Tqualified cv <$> t ();
  |}.

  (** Just traverse *)
  Definition handle_expr_traverse : expr_handler F := {|
    handle_Eparam X := mret $ Eparam X;
    handle_Eunresolved_global _ n := Eunresolved_global <$> n ();
    handle_Eunresolved_unop o _ e := Eunresolved_unop o <$> e ();
    handle_Eunresolved_binop o _ _ l r := Eunresolved_binop o <$> l () <*> r ();
    handle_Eunresolved_call _ _ n es := Eunresolved_call <$> n () <*> sequence@{eta list} (es ());
    handle_Eunresolved_member_call _ _ _ n e es := Eunresolved_member_call <$> n () <*> e () <*> sequence@{eta list} (es ());
    handle_Eunresolved_parenlist _ _ t es := Eunresolved_parenlist <$> sequence@{eta option} (t ()) <*> sequence@{eta list} (es ());
    handle_Eunresolved_member _ _ o f := Eunresolved_member <$> o () <*> f ();
    handle_expr_type := id;
    handle_Eunresolved_cast _ Mt _ Me := (fun t e => Ecast (Cdependent t) e) <$> Mt () <*> Me () ;
    handle_unresolved_init _ mt oe :=
      match oe with
      | None => (fun t => (t, None)) <$> mt ()
      | Some e => pair <$> mt () <*> (Some <$> e.2 ())
      end
  |}.
End handlers.

(**
TODO: Adjust <<#[only(lens)] derive>> to support (primitive
projections and) universe polymorphic records, then derive a full set
of lenses for the handler types.
*)
Section lens.
  Universe u.
  Context {N T E : Type@{u}}.
  #[local] Notation type_handler := (type_handler' N T E).

  Definition _handle_Tnamed : type_handler ~l> name -> (unit -> N) -> T  := {|
    Lens.view r := r.(handle_Tnamed);
    Lens.over f r := {|
      handle_Tparam := r.(handle_Tparam);
      handle_Tresult_param := r.(handle_Tresult_param);
      handle_Tresult_global := r.(handle_Tresult_global);
      handle_Tresult_unop := r.(handle_Tresult_unop);
      handle_Tresult_binop := r.(handle_Tresult_binop);
      handle_Tresult_call := r.(handle_Tresult_call);
      handle_Tresult_member_call := r.(handle_Tresult_member_call);
      handle_Tresult_parenlist := r.(handle_Tresult_parenlist);
      handle_Tresult_member := r.(handle_Tresult_member);
      handle_Tnamed := f r.(handle_Tnamed);
      handle_Tref := r.(handle_Tref);
      handle_Trv_ref := r.(handle_Trv_ref);
      handle_Tqualified := r.(handle_Tqualified);
    |};
  |}.

  Definition _handle_Tref : type_handler ~l> _  := {|
    Lens.view r := r.(handle_Tref);
    Lens.over f r := {|
      handle_Tparam := r.(handle_Tparam);
      handle_Tresult_param := r.(handle_Tresult_param);
      handle_Tresult_global := r.(handle_Tresult_global);
      handle_Tresult_unop := r.(handle_Tresult_unop);
      handle_Tresult_binop := r.(handle_Tresult_binop);
      handle_Tresult_call := r.(handle_Tresult_call);
      handle_Tresult_member_call := r.(handle_Tresult_member_call);
      handle_Tresult_parenlist := r.(handle_Tresult_parenlist);
      handle_Tresult_member := r.(handle_Tresult_member);
      handle_Tnamed := r.(handle_Tnamed);
      handle_Tref := f r.(handle_Tref);
      handle_Trv_ref := r.(handle_Trv_ref);
      handle_Tqualified := r.(handle_Tqualified);
    |};
  |}.
  Definition _handle_Trv_ref : type_handler ~l> _ := {|
    Lens.view r := r.(handle_Trv_ref);
    Lens.over f r := {|
      handle_Tparam := r.(handle_Tparam);
      handle_Tresult_param := r.(handle_Tresult_param);
      handle_Tresult_global := r.(handle_Tresult_global);
      handle_Tresult_unop := r.(handle_Tresult_unop);
      handle_Tresult_binop := r.(handle_Tresult_binop);
      handle_Tresult_call := r.(handle_Tresult_call);
      handle_Tresult_member_call := r.(handle_Tresult_member_call);
      handle_Tresult_parenlist := r.(handle_Tresult_parenlist);
      handle_Tresult_member := r.(handle_Tresult_member);
      handle_Tnamed := r.(handle_Tnamed);
      handle_Tref := r.(handle_Tref);
      handle_Trv_ref := f r.(handle_Trv_ref);
      handle_Tqualified := r.(handle_Tqualified);
    |};
  |}.

End lens.
