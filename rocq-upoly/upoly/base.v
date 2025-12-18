(*
 * Copyright (c) 2023-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.upoly.prelude.

(**
We aim to be compatible with stdpp and SSR.

Recall
- \/ (right) at 85
- <$> (right) at 61
- >>= (right), ++ (right) at 60
- || (left), + (left) at 50
- && (left) at 40
*)

Reserved Notation "'let*' x , .. , z := t 'in' f" (at level 200, x closed binder, z closed binder).
Reserved Notation "'let*' := t 'in' f" (at level 200).
Reserved Notation "'letM*' x , .. , z := t 'in' f" (at level 200, x closed binder, z closed binder).
Reserved Notation "'letM*' := t 'in' f" (at level 200).
Reserved Notation "'funM' x .. y => t" (at level 200, x binder, y binder, right associativity).

Reserved Infix "`catch`" (at level 101, right associativity).

Reserved Infix "<*>" (at level 61, left associativity).
Reserved Infix "<*>@{ F }" (at level 61, left associativity).

Reserved Infix ">>=" (at level 60, right associativity).
Reserved Infix ">>=@{ M }" (at level 60, right associativity).
Reserved Infix "<|>" (at level 60, right associativity).
Reserved Infix "<|>@{ F } " (at level 60, right associativity).

Reserved Infix "<*" (at level 60, right associativity).
Reserved Infix "*>" (at level 60, right associativity).

Reserved Notation "f \o g" (at level 50, format "f  \o '/ '  g").

Declare Scope monad_scope.
Delimit Scope monad_scope with M.

(** ** Universe polymorphic classes *)
(**
<<Import UPoly>> shadows a few (standard definitions and) stdpp type
classes with universe polymorphic variants, adjusting <<stdpp_scope>>
to refer to them.

Take care when declaring instances of universe polymorphic type
classes.

- For universe polymorphic types, be direct (e.g., <<MRet T>>).

- For template universe polymorphic types, eta expand (e.g., <<MRet
(eta option)>>).
*)
Module Import UPoly.

  Notation relation A := (A -> A -> Prop)%type (only parsing).

  Notation id := (fun x => x) (only parsing).

  Notation const x := (fun _ => x) (only parsing).
  Notation const1 x := (fun _ => x) (only parsing).
  Notation const2 x := (fun _ _ => x) (only parsing).
  Notation const3 x := (fun _ _ _ => x) (only parsing).
  Notation const4 x := (fun _ _ _ _ => x) (only parsing).
  Notation const5 x := (fun _ _ _ _ _ => x) (only parsing).
  Notation const6 x := (fun _ _ _ _ _ _ => x) (only parsing).
  Notation const7 x := (fun _ _ _ _ _ _ _ => x) (only parsing).

  Notation eta f := (fun a => f a) (only parsing).

  Definition compose@{uA uB uC | }
      {A : Type@{uA}} {B : Type@{uB}} {C : Type@{uC}}
      (g : B -> C) (f : A -> B) (x : A) : C :=
    g (f x).
  Infix "\o" := compose : stdpp_scope.

  (** ** Functors *)

  Class FMap@{u1 u2 uB} (M : Type@{u1} -> Type@{u2}) :=
    fmap : ∀ {A : Type@{u1}} {B : Type@{uB}}, (A -> B) -> M A -> M B.
  #[global] Hint Mode FMap ! : typeclass_instances.
  #[global] Instance fmap_params : Params (@fmap) 4 := {}.
  #[global] Arguments fmap _ _ _ _ _ & !_ / : assert.
  #[global] Hint Opaque fmap : typeclass_instances.

  Class MRet@{u1 u2} (M : Type@{u1} -> Type@{u2}) :=
    mret : ∀ {A : Type@{u1}}, A -> M A.
  #[global] Hint Mode MRet ! : typeclass_instances.
  #[global] Instance ret_params : Params (@mret) 3 := {}.
  #[global] Arguments mret _ _ _ & _ : assert.
  #[global] Hint Opaque mret : typeclass_instances.

  Class Ap@{u1 u2 uA uB} (F : Type@{u1} -> Type@{u2}) :=
    ap : ∀ {A : Type@{uA}} {B : Type@{uB}}, F (A -> B) -> F A -> F B.
  #[global] Hint Mode Ap ! : typeclass_instances.
  #[global] Arguments ap {_ _ _ _} & _ !_ / : simpl nomatch, assert.
  #[global] Instance: Params (@ap) 4 := {}.
  #[global] Hint Opaque ap : typeclass_instances.

  (** ** Traversable types *)

  Class Traverse@{u1 u2 v1 v2 uA uB uB'} (T : Type@{u1} -> Type@{u2}) : Type :=
    traverse : ∀ {F : Type@{v1} -> Type@{v2}}
      `{!FMap@{v1 v2 uB} F, !MRet@{v1 v2} F, AP : !Ap@{v1 v2 uA uB'} F}
       {A : Type@{u1}} {B : Type@{v1}}, (A -> F B) -> T A -> F (T B).
  #[global] Hint Mode Traverse ! : typeclass_instances.
  #[global] Instance traverse_params : Params (@traverse) 8 := {}.
  #[global] Arguments traverse _ _ _ _ _ _ _ _ & _ !_ / : assert.
  #[global] Hint Opaque traverse : typeclass_instances.

  (**
  We make [sequence] an abbreviation for [traverse id].

  We could define a type class [Sequence], making [traverse id] the
  default instance. Presently, that flexibility would buy us nothing but
  cost us something. To reason about [sequence], for example, we would
  either have to specialize/duplicate the theory of [traverse] or unfold
  [sequence] where it shows up.
  *)
  Notation sequence := (traverse id).
  Notation "sequence@{ A }" := (traverse (T:=A) id) (only parsing).

  (** ** Alternative *)

  (** << p <|> q >> computes <<p>> and, if that fails, behaves like <<q ()>> *)
  Class Alternative@{u1 u2 | } (F : Type@{u1} -> Type@{u2}) :=
    alternative : ∀ {A : Type@{u1}}, F A -> (unit -> F A) -> F A.
  #[global] Hint Mode Alternative ! : typeclass_instances.
  #[global] Instance alternative_params : Params (@alternative) 3 := {}.
  #[global] Arguments alternative _ _ _ & !_ !_ / : simpl nomatch, assert.
  #[global] Hint Opaque alternative : typeclass_instances.

  (** ** Monads *)

  Class MBind@{u1 u2} (M : Type@{u1} -> Type@{u2}) :=
    mbind : ∀ {A B : Type@{u1}}, (A -> M B) -> M A -> M B.
  #[global] Hint Mode MBind ! : typeclass_instances.
  #[global] Instance bind_params : Params (@mbind) 4 := {}.
  #[global] Arguments mbind _ _ _ _ & _ !_ / : assert.
  #[global] Hint Opaque mbind : typeclass_instances.

  Class MJoin@{uA uM} (M : Type@{uM} -> Type@{uM}) :=
    mjoin : ∀ {A : Type@{uA}}, M (M A) -> M A.
  #[global] Hint Mode MJoin ! : typeclass_instances.
  #[global] Instance join_params : Params (@mjoin) 3 := {}.
  #[global] Arguments mjoin _ _ _ & !_ / : simpl nomatch, assert.
  #[global] Hint Opaque mjoin : typeclass_instances.

  (** ** Errors *)

  (** Throw errors of type <<E>> *)
  Class MThrow@{uE u1 u2 | } (E : Type@{uE}) (M : Type@{u1} -> Type@{u2}) :=
    mthrow : ∀ {A}, E -> M A.
  #[global] Hint Mode MThrow ! ! : typeclass_instances.
  #[global] Instance mthrow_params : Params (@mthrow) 4 := {}.
  #[global] Arguments mthrow {_ _ _ _} _ : assert.
  #[global] Hint Opaque mthrow : typeclass_instances.

  (** <<catch m h>> tries <<m>>, applying handler <<h>> on error *)
  Class MCatch@{uE u1 u2} (E : Type@{uE}) (M : Type@{u1} -> Type@{u2}) :=
    mcatch : ∀ {A}, M A -> (E -> M A) -> M A.
  #[global] Hint Mode MCatch ! ! : typeclass_instances.
  #[global] Hint Mode MCatch - + : typeclass_instances.
  #[global] Instance mcatch_params : Params (@mcatch) 4 := {}.
  #[global] Arguments mcatch _ _ _ _ & _ _ : assert.
  #[global] Hint Opaque mcatch : typeclass_instances.

  (** Extend the backtrace on failure *)
  Class Trace@{uE u1 u2 | } (E : Type@{uE}) (M : Type@{u1} -> Type@{u2}) :=
    trace : E -> ∀ {A : Type@{u1}}, M A -> M A.
  #[global] Hint Mode Trace ! ! : typeclass_instances.
  #[global] Instance trace_params : Params (@trace) 5 := {}.
  #[global] Arguments trace _ _ _ _ _ & !_ / : simpl nomatch, assert.
  #[global] Hint Opaque trace : typeclass_instances.

  (** Compute a proof of [P] or fail with error <<e>> *)
  Definition guard_or@{uE u1 u2 | } {E : Type@{uE}} (e : E)
      {M : Type@{u1} -> Type@{u2}} `{!MThrow E M, !MRet M}
      (P : Prop) `{dec : !Decision P} : M P :=
    match dec with
    | left HP => mret HP
    | right _ => mthrow e
    end.
  #[global] Arguments guard_or _ _ _ _ _ _ !_ / : simpl nomatch, assert.
  #[global] Instance guard_or_params : Params (@guard_or) 7 := {}.
  #[global] Hint Opaque guard_or : typeclass_instances.

  (** Errors without context *)
  #[global] Notation MFail := (MThrow ()).
  #[global] Notation mfail := (mthrow ()).
  #[global] Notation guard := (guard_or ()).

  (** ** Lifting *)

  (** Lift a computation *)
  Class MLift@{u1 u2 v1 v2} (M1 : Type@{u1} -> Type@{u2})
      (M2 : Type@{v1} -> Type@{v2}) :=
    mlift : ∀ {A : Type@{u1}}, M1 A -> M2 A.
  #[global] Hint Mode MLift ! ! : typeclass_instances.
  #[global] Hint Mode MLift - + : typeclass_instances.
  #[global] Instance lift_params : Params (@mlift) 4 := {}.
  #[global] Arguments mlift _ _ _ _ & _ : assert.
  #[global] Hint Opaque mlift : typeclass_instances.

  (** ** Notation *)

  (**
  We put most notation in <<stdpp_scope>> (open by default).

  We put notation with other purposes, like <<let*>>, in
  <<monad_scope>> (not open by default).

  One can locally open <<monad_scope>> (e.g., via <<funM>>,
  <<letM*>>).

  We bundle these effects so they can be replayed.
  *)
  Module Export Notations.

    Notation "'funM' x .. y => t" :=
      (fun x => .. (fun y => t%M) ..) (only parsing) : function_scope.
    Notation "'letM*' x , .. , z := t 'in' f" :=
      (mbind (fun x => .. (fun z => f) ..) t%M) (only parsing) : stdpp_scope.
    Notation "'letM*' := t 'in' f" :=
      (mbind (fun _ : unit => f) t%M) (only parsing) : stdpp_scope.

    Infix "<$>" := fmap : stdpp_scope.

    Infix "<*>" := ap : stdpp_scope.
    Infix "<*>@{ F }" := (ap (F:=F)) (only parsing) : stdpp_scope.

    Notation "a <* b" := ((fun l _ => l) <$> a <*> b) : stdpp_scope.
    Notation "a *> b" := ((fun _ r => r) <$> a <*> b) : stdpp_scope.

    Notation "p <|> q" := (alternative p (fun _ : unit => q)) : stdpp_scope.
    Notation "p <|>@{ F } q" := (alternative (F:=F) p (fun _ : unit => q)) (only parsing) : stdpp_scope.

    Notation "m >>= f" := (mbind f m) : stdpp_scope.
    Notation "m >>=@{ M } f" := (mbind (M:=M) f m) (only parsing) : stdpp_scope.
    Notation "( m >>=.)" := (fun f => mbind f m) (only parsing) : stdpp_scope.
    Notation "(.>>= f )" := (mbind f) (only parsing) : stdpp_scope.
    Notation "(>>=)" := mbind (only parsing) : stdpp_scope.
    Notation "p ;; q" := (p >>= fun _ => q) (only parsing) : stdpp_scope.

    Notation "x ← m ; e" := (mbind (fun x => e) m) (only parsing) : stdpp_scope.

    Infix "`catch`" := mcatch : stdpp_scope.

    Notation "'let*' x , .. , z := t 'in' f" :=
      (mbind (fun x => .. (fun z => f) ..) t) (only parsing) : monad_scope.
    Notation "'let*' := t 'in' f" :=
      (mbind (fun _ : unit => f) t) (only parsing) : monad_scope.

  End Notations.

  (** ** Default Instances *)
  (**
  NOTE: We assume monadic operations to be cheaper than applicative
  operatations (reflected in the costs).
  *)

  #[global] Instance monad_fmap {M} `{!MBind M, !MRet M} : FMap M | 1000 :=
    fun _ _ f m => m >>= fun x => mret (f x).
  #[global] Arguments monad_fmap _ _ _ _ _ _ _ / : assert.

  #[global] Instance applicative_fmap {F} `{!MRet F, !Ap F} : FMap F | 1010 :=
    fun _ _ f => ap (mret f).
  #[global] Arguments applicative_fmap _ _ _ _ _ _ _ / : assert.

  #[global] Instance monad_ap {M} `{!MBind M, !MRet M} : Ap M | 1000 := funM _ _ mf ma =>
    let* f := mf in let* a := ma in mret (f a).
  #[global] Arguments monad_ap _ _ _ _ _ _ _ / : simpl nomatch, assert.

  #[global] Instance catch_alternative {M E} `{!MCatch E M} : Alternative M | 1000 := fun _ p q =>
    p `catch` fun _ => q ().

  (** ** Instances *)

  (** [Datatypes.option] *)

  #[global] Instance option_fmap : FMap (eta option) := fun _ _ f m =>
    if m is Some a then Some (f a) else None.
  #[global] Instance option_ret : MRet (eta option) := @Some.
  #[global] Instance option_bind : MBind (eta option) := fun _ _ f m =>
    if m is Some a then f a else None.
  #[global] Instance option_join : MJoin (eta option) := fun _ m =>
    if m is Some o then o else None.
  Succeed Definition option_ap : Ap (eta option) := _.
  #[global] Instance option_traverse : Traverse (eta option) := fun _ _ _ _ _ _ f m =>
    if m is Some a then Some <$> f a else mret None.
  #[global] Instance option_fail : MFail (eta option) := fun _ _ => None.
  #[global] Instance option_catch : MCatch unit (eta option) := fun _ m h =>
    if m is Some _ then m else h ().
  Succeed Definition option_alternative : Alternative (eta option) := _.

  (** [Datatypes.list] *)

  #[global] Instance list_fmap : FMap (eta list) := fun A B f =>
    fix go (xs : list A) : list B :=
    match xs with
    | nil => nil
    | x :: xs => f x :: go xs
    end.
  #[global] Instance list_ret : MRet (eta list) := fun _ x => [x].
  #[global] Instance list_bind : MBind (eta list) := fun A B (f : A -> list B) =>
    fix go (xs : list A) : list B :=
    match xs with
    | nil => nil
    | x :: xs => f x ++ go xs
    end.
  #[global] Instance list_join : MJoin (eta list) := fun A =>
    fix go (ls : list (list A)) : list A :=
    match ls with
    | nil => nil
    | l :: ls => l ++ go ls
    end.
  Succeed Definition list_ap : Ap (eta list) := _.
  #[global] Instance list_traverse : Traverse (eta list) := fun F _ _ AP A B (f : A -> F B) =>
    fix go (l : list A) : F (list B) :=
    match l with
    | [] => mret []
    | x :: l => cons <$> f x <*> go l
    end.
  #[global] Instance list_fail : MFail (eta list) := fun _ _ => nil.
  #[global] Instance list_catch : MCatch unit (eta list) := fun _ l h =>
    if l is nil then h () else l.
  Succeed Definition list_alternative : Alternative (eta list) := _.

  (** [Datatypes.sum] *)

  Section sum_fmap.
    Universes uA uB uA' uB'.
    Constraint uA <= sum.u0, uA' <= sum.u0.
    Constraint uB <= sum.u1, uB' <= sum.u1.
    Context {A : Type@{uA}} {B : Type@{uB}} {A' : Type@{uA'}} {B' : Type@{uB'}}.

    Definition sum_fmap (f : A -> A') (g : B -> B') (s : A + B) : A' + B' :=
      match s with
      | inl a => inl $ f a
      | inr b => inr $ g b
      end.
    #[global] Hint Opaque sum_fmap : typeclass_instances.
    #[global] Arguments sum_fmap _ _ & _ : assert.
  End sum_fmap.

  Section sum_traverse.
    Universes u1 u2 uS uA uB uA' uB'.
    Constraint uS <= u1.
    Constraint uA <= sum.u0, uA' <= sum.u0, uA' <= uS.
    Constraint uB <= sum.u1, uB' <= sum.u1, uB' <= uS.
    Context {F : Type@{u1} -> Type@{u2}} `{!FMap@{u1 u2 uS} F, !MRet F}.
    Context {A : Type@{uA}} {B : Type@{uB}} {A' : Type@{uA'}} {B' : Type@{uB'}}.

    Definition sum_traverse (f : A -> F A') (g : B -> F B') (s : sum A B) : F (sum A' B') :=
      match s with
      | inl a => inl <$> f a
      | inr b => inr <$> g b
      end.
    #[global] Hint Opaque sum_traverse : typeclass_instances.
    #[global] Arguments sum_traverse _ _ & _ : assert.
  End sum_traverse.

  #[global] Instance sum_ret_right {E} : MRet (eta (sum E)) := fun _ x => inr x.
  #[global] Instance sum_fmap_right {E} : FMap (eta (sum E)) := fun _ _ f x =>
    match x with
    | inl err => inl err
    | inr v => inr $ f v
    end.
  #[global] Instance sum_bind_right {E} : MBind (eta (sum E)) := fun _ _ k c =>
    match c with
    | inl err => inl err
    | inr v => k v
    end.
  #[global] Instance sum_join_right {E} : MJoin (eta (sum E)) := fun _ c =>
    match c with
    | inr (inr _ as c) => c
    | inl err | inr (inl err) => inl err
    end.
  #[global] Instance sum_traverse_right {E} : Traverse (eta (sum E)) := fun _ _ _ _ _ _ f s =>
    match s with
    | inl x => mret (inl x)
    | inr y => inr <$> f y
    end.

  (** [Datatypes.prod] *)

  Section prod_fmap.
    Universes uA uB uA' uB'.
    Constraint uA <= prod.u0, uA' <= prod.u0.
    Constraint uB <= prod.u1, uB' <= prod.u1.
    Context {A : Type@{uA}} {B : Type@{uB}} {A' : Type@{uA'}} {B' : Type@{uB'}}.

    Definition prod_fmap (f : A -> A') (g : B -> B') (p : A * B) : A' * B' :=
      match p with
      | (a, b) => (f a, g b)
      end.
    #[global] Hint Opaque prod_fmap : typeclass_instances.
    #[global] Arguments prod_fmap _ _ & !_ / : simpl nomatch, assert.
  End prod_fmap.

  Section prod_traverse.
    Universes u1 u2 uL uR.
    Constraint uL <= u1, uR <= u1.
    Context {F : Type@{u1} -> Type@{u2}} `{!FMap@{u1 u2 uR} F, !MRet F, AP : !Ap@{u1 u2 uL uR} F}.

    Universes uA uB uA' uB'.
    Constraint uA <= prod.u0, uA' <= prod.u0, uA' <= uR.
    Constraint uB <= prod.u1, uB' <= prod.u1, uB' <= uL, uB' <= uR.
    Context {A : Type@{uA}} {B : Type@{uB}} {A' : Type@{uA'}} {B' : Type@{uB'}}.
    Definition prod_traverse (f : A -> F A') (g : B -> F B') (p : prod A B) : F (prod A' B') :=
      match p with
      | (a, b) => pair <$> f a <*> g b
      end.
    #[global] Hint Opaque prod_traverse : typeclass_instances.
    #[global] Arguments prod_traverse _ _ & _ : assert.
  End prod_traverse.

  #[global] Instance pair_traverse_right {E} : Traverse (eta (prod E)) :=
    fun _ _ _ _ _ _ f p =>
    match p with
    | (a, b) => pair a <$> f b
    end.
  #[global] Arguments pair_traverse_right _ _ _ _ _ _ _ _ & !_ / : simpl nomatch, assert.

End UPoly.

Definition first {T T' U} (f : T -> T') (xy : T * U) : T' * U := (f xy.1, xy.2).
Definition second {T U U'} (f : U -> U') (xy : T * U) : T * U' := (xy.1, f xy.2).
