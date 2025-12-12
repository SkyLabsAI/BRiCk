(*
 * Copyright (C) 2020-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import Stdlib.Strings.PrimString.
Require Import bluerock.prelude.base.
Require Export bluerock.prelude.tactics.base_dbs.
Require bluerock.ltac2.extra.extra.

Export PStringNotations.

Require Ltac2.Ltac2.
Require Ltac2.Pstring.

(** NamedBinder is a type wrapper that can be used to record the name
    of a binder in a persistent way that is not affected by any computation.

    Existentials/universals of type [NamedBinder A str] are always
    eliminated/introduced directly as an assumption named [str] of type [A].
 *)
Definition NamedBinder (A:Type) (name : string) := A.
#[global] Arguments NamedBinder : simpl never.
#[global] Hint Opaque NamedBinder : typeclass_instances br_opacity.

Module Binder.
  Import Ltac2.
  Import Ltac2.Printf.
  Import Ltac2.Constr.
  Import Ltac2.Constr.Unsafe.
  Import Ltac2.Pstring.

  Ltac2 Type exn ::= [Impossible].

  Ltac2 binder (p : constr) :=
    (* printf "%t" p; *)
    let id := match Constr.Unsafe.kind p with
    | Constr.Unsafe.Lambda b _ =>
        (Option.default (@anon) (Constr.Binder.name b))
    | _ => @anon
    end in
    let str :=
      match Pstring.of_string (Ident.to_string id) with
      | Some s => s
      | None => Option.get (Pstring.of_string "anon")
      end
    in
    Unsafe.make (String str).

  Ltac2 binder_ltac1 (p : Ltac1.t) :=
    let p := Option.get (Ltac1.to_constr p) in
    refine (binder p).

  (* Solve the goal with [fun (x : s) => x] *)
  Ltac2 to_id_fun (s : constr) : unit :=
    let str :=
      match kind s with
      | String s => Pstring.to_string s
      | _ => Control.throw (Invalid_argument None)
      end
    in
    let id := Ident.of_string str in
    let binder := Constr.Binder.make id 'unit in
    let f := Constr.Unsafe.make (
        Constr.Unsafe.Lambda binder (Constr.Unsafe.make (Constr.Unsafe.Rel 1))
      )
    in
    refine f.

  Ltac id_of := ltac2:(str |- to_id_fun (Option.get (Ltac1.to_constr str))).

  Import bluerock.ltac2.extra.extra.
  Import Constr.Unsafe.

  (* Passing [true] to the first argument will remove occurances of [NamedBinder]
     when they do not occur in products or lambdas.
   *)
  Ltac2 name_binders (b : bool) (c : constr) : constr :=
    let get_name name :=
      match kind name with
      | String name => Pstring.to_string name
      | _ => let name := Std.eval_vm None name in
             match kind name with
             | String name => Pstring.to_string name
             | _ => throw_invalid! "Unreduced primitive string"
             end
      end
    in
    let rec go c :=
      match kind c with
      | Lambda b t =>
          let t := go t in
          let b :=
            lazy_match! Binder.type b with
            | NamedBinder ?ty ?name =>
                let b := Constr.Binder.map_type (fun _ => ty) b in
                let name := get_name name in
                let name := Ident.of_string name in
                Constr.Binder.map_name (fun _ => name) b
            | _ => b
            end
          in
          make_lambda b t
      | Prod b t =>
          let t := go t in
          let b :=
            lazy_match! Binder.type b with
            | NamedBinder ?ty ?name =>
                let b := Constr.Binder.map_type (fun _ => ty) b in
                let name := get_name name in
                let name := Ident.of_string name in
                Constr.Binder.map_name (fun _ => name) b
            | _ => b
            end
          in
          make_prod b t
      | App _ _ =>
          if b then
            lazy_match! c with
            | NamedBinder ?x _ => go x
            | _ => Constr.Unsafe.map go c
            end
          else
            Constr.Unsafe.map go c
      | _ => Constr.Unsafe.map go c
      end
    in
    go c.

  Ltac2 with_binder_cps k f :=
    let b := binder f in
    let t := make_app2 k f b in
    t.

  Ltac2 with_binder_cps_ltac1 k f :=
    let k := Option.get (Ltac1.to_constr k) in
    let f := Option.get (Ltac1.to_constr f) in
    Std.exact_no_check (with_binder_cps k f).
End Binder.

(* [TCForceEq] disregards typeclass_instances opacity.  *)
Inductive TCForceEq {A : Type} (x : A) : A -> Prop :=  TCForceEq_refl : TCForceEq x x.
Existing Class TCForceEq.
#[global] Hint Extern 100 (TCForceEq ?x _) => refine (TCForceEq_refl x) : typeclass_instances.

Class IdOfBS (name : string) (ident : () -> ()) := ID_OF_BS {}.
#[global] Arguments IdOfBS name _%_function_scope.
#[global] Hint Mode IdOfBS ! - : typeclass_instances.

#[global] Hint Extern 100 (IdOfBS ?name _) =>
  refine (@ID_OF_BS name ltac:(Binder.id_of name)) : typeclass_instances.

(** Infrastructure to get names into terms using Ltac2 and a type class called
    [Binder]. Using [Binder] in recursive notation risks dangling evars. See
    [BinderCPS] for a better alternative. *)
Section Binder.
  #[local] Set Typeclasses Unique Instances.
  #[local] Set Typeclasses Strict Resolution.
  (** [Binder (fun x => _)] resolves to ["x"]. *)
  Class Binder {P : Type} (p : P) := binder : string.
End Binder.

Hint Opaque Binder : typeclass_instances.
Ltac binder := ltac2:(p |- Binder.binder_ltac1 p).
#[global] Hint Extern 0 (Binder ?p) => binder p : typeclass_instances.

(** NOTE: The [binder x] notation can leave dangling evars when the binder [x]
    has no type annotation. Rocq will often clean up these dangling evars but
    they interact badly with tactics in terms. It is recommended to use
    [BinderCPS] instead. *)
#[deprecated(since="20250710", note="Use [BinderCPS] to avoid dangling evars.")]
#[global] Notation "'[binder' x ]" :=
  (_ :> @Binder (forall x, True) (fun x => I)) (at level 0, x binder, only parsing).


Section CPS.
  Variant dummy_prop : Prop := DummyValue.

  #[local] Set Typeclasses Unique Instances.
  #[local] Set Typeclasses Strict Resolution.
  (** The class [BinderCPS] can be used on applications of higher-order
      functions to feed the name of the binder of the function argument to the
      higher-order function.

      [_ :> BinderCPS (k (fun x => t))] resolves to [k (fun x => t) "x"].

      The corresponding notation, [with_binder (k (fun x => t))], elaborates to
      [k (fun x => t) "x" DummyValue]. Note that this requires
      [k : (?A -> ?B) -> string -> dummy_prop -> ?T].

      The extra [dummy_prop] argument is necessary because the result of
      [with_binder (k f)] has type [@BinderCPS ?T _ (k f)], not [?T]. This can
      block typeclass search. In order to force Rocq to unfold the type to [?T]
      we have to instantiate it with a function type and apply the term to another argument.
      We pick [T := dummy_prop -> ?T']. *)
  Class BinderCPS {T} (kf : PrimString.string -> dummy_prop -> T) := my_binder : dummy_prop -> T.
End CPS.

#[global] Notation "'[with_binder' kf ]" := ((_ :> BinderCPS kf) DummyValue) (at level 0, only parsing).
Ltac with_binder_cps := ltac2:(k f |- Binder.with_binder_cps_ltac1 k f).
#[global] Hint Extern 0 (BinderCPS (?k ?f)) => with_binder_cps k f : typeclass_instances.
