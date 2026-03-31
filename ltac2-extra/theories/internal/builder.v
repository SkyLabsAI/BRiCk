
Require Import skylabs.ltac2.extra.internal.init.
Require Import skylabs.ltac2.extra.internal.constr.
Require Import skylabs.ltac2.extra.internal.int.
Require Import skylabs.ltac2.extra.internal.list.
Require Import skylabs.ltac2.extra.internal.string.

Require Import skylabs.ltac2.extra.internal.control.
Require Import skylabs.ltac2.extra.internal.printf.
Require Import skylabs.ltac2.extra.internal.fset.
Require Import skylabs.ltac2.extra.internal.fmap.

Require Import Stdlib.Strings.PrimString.

Import Ltac2 Init.

(** ['a Builder.t] provides a function ['a -> constr] to turn an Ltac2 value into a Gallina term.
    Builders can be combined to build bigger builders. If one defines a Ltac2 type [foo] and a
    builder [build_foo] for it, one can use it to turn [xs : foo option list] into a term with
    [run (build_list (build_option build_foo)) xs]. *)
Module Builder.
  Import Ltac2 Init Constr Printf.
  Import Control.Notations.

  Ltac2 Type 'a impl := { type : constr; build : 'a -> constr }.
  Ltac2 Type 'a t := unit -> 'a impl.

  Ltac2 Type arg := [ Wildcard | WildcardWithType(constr) | Term(constr) ].

  Module Arg.

    Ltac2 map (f : constr -> constr) (a : arg) : arg :=
      match a with
      | Term trm => Term (f trm)
      | Wildcard => Wildcard
      | WildcardWithType ty => WildcardWithType (f ty)
      end.

    Ltac2 term (a : arg) : constr :=
      match a with
      | Term trm => trm
      | Wildcard => '(_)
      | WildcardWithType ty => Evar.make ty
      end.

    Ltac2 pp : arg pp :=
      fun () a =>
        match a with
        | Wildcard => fprintf "?"
        | WildcardWithType ty => fprintf "? : %t" ty
        | Term x => fprintf "%t" x
        end.

    Ltac2 pp_typed : arg pp :=
      fun () a =>
        match a with
        | Wildcard => fprintf "? : ?"
        | WildcardWithType ty => fprintf "? : %t" ty
        | Term x => fprintf "%t : %t" x (Constr.type x)
        end.

  End Arg.

  Module Constr.
  Module Unsafe.

    (** For a term [forall x y z, F x y z], return a set of integers that identify which of the bound
        variables [x,y,z] are referenced. Contrary to the de Bruijn encoding, [x] is referenced to as
        1, [y] 2, and [z] instead of 3,2,1 respectively. This gives us references that are relative to
        the first binder instead of the last. Any [Rel] not bound in that list of variables will be
        omitted.

        The resulting set of integers are paired to the (optional) name given to it by the binder the
        variables refer to.

        The only binders considered are consecutive top level binders. The binders occurring in the
        type or definitions of variables are ignored -- otherwise, each referenced variable may refer
        to different names at different places.
        NOTE: if the names are not needed, the types and definitions could be treated the same way as the body.

        [let] and [fun] binders are treated similarly to [forall].
     *)
    Ltac2 bound_rel_occurrences (trm : constr)  : (int, name) FMap.t :=
      let empty_set := FSet.empty FSet.Tags.int_tag in
      let free_rels (bump : int) (trm : constr) : int FSet.t :=
        let vars := Vars.rels trm in
        let sub i :=
          if Int.lt i bump then
            Some (Int.sub bump i)
          else
            None in
        let vars := List.map_filter sub vars in
        let tag  := FSet.Tags.int_tag in
        FSet.of_list tag vars in

      let to_binder (trm : constr) :=
        match Unsafe.kind trm with
        | Unsafe.Prod bnd bod => Some (bnd, None, bod)
        | Unsafe.Lambda bnd bod => Some (bnd, None, bod)
        | Unsafe.LetIn bnd def bod => Some (bnd, Some def, bod)
        | _ => None
        end in

      (** [name_map] - collects the names of all binders encountered during term traversal
          [occ]      - collects the level numbers of binders referenced along the traversal  *)
      let rec go trm occ idx name_map :=
        match to_binder trm with
        | Some (bnd, def, bod) =>
          let ty := Binder.type bnd in
          let n := Binder.name bnd in
          let idx' := Int.add idx 1 in
          let name_map' := FMap.add idx n name_map in
          let occ' :=
            let free_ty := free_rels idx ty in
            let free_def := Option.map_default (free_rels idx) empty_set def in
            let free := FSet.union free_ty free_def in
            FSet.union occ free in
          go bod occ' idx' name_map'
        | None =>
            let free := free_rels idx trm in
            let occ'  := FSet.union free occ in
            FMap.filteri (fun k _v => FSet.mem k occ') name_map
        end in
      let map := FMap.empty FSet.Tags.int_tag in
      go trm empty_set 1 map.


    (** [instantiate_prod ty args], with [ty] a product type and args a list of (possibly omitted)
        arguments produces [(args', ty')] with [ty'] the result of instantiating [length args] bound
        variables and [args'] the arguments and evars used in the instantiation.

        Each argument can be one of:
          * Wildcard            - when the argument is omitted;
          * WithcardWithType ty - when the argument is omitted but its type is specified;
          * Term x              - when [x] is the provided argument.

        POSSIBLE ADDITION: a third argument [future_arguments : int] so that [args] doesn't have to
        match from the beginning.  [instantiate_prod '(@List.append) [Term '([1;2])] 1] would produce
        the type [list nat -> list nat], i.e. a function taking one (1) more argument, and [['(nat); [1;2]]]. *)
    Ltac2 instantiate_prod (ty : constr) (args : arg list) : arg list * constr :=
      let occurs := Constr.Unsafe.bound_rel_occurrences ty in
      let dud := '(True) in
      let mk_evar idx ty :=
        if FMap.mem idx occurs then
          let x := Constr.Evar.make ty in
          (x, Term x)
        else
          (dud, WildcardWithType ty) in
      let rec go ty idx args subst acc :=
        match args with
        | [] => (List.rev acc, Constr.Unsafe.substnl subst 0 ty)
        | x :: xs =>
            match Constr.Unsafe.kind ty with
            | Constr.Unsafe.Prod bnd bod =>
                let arg_ty := Constr.Binder.type bnd in
                let arg_ty := Constr.Unsafe.substnl subst 0 arg_ty in
                let (x, arg) :=
                  match x with
                  | Wildcard =>
                      mk_evar idx arg_ty
                  | WildcardWithType x_ty =>
                      Std.unify x_ty arg_ty ;
                      mk_evar idx x_ty
                  | Term x =>
                      let x_ty := Constr.type x in
                      Std.unify x_ty arg_ty ;
                      (x, Term x)
                  end in
                let idx'   := Int.add idx 1 in
                let subst' := x :: subst in
                let acc'   := arg :: acc in
                go bod idx' xs subst' acc'
            | _ =>
                let msg := fprintf "instantiate_prod: excess arguments%a%a"
                             (pp_lines pp_string) [""]
                             (pp_lines (pp_prefix "  - " Arg.pp))
                             xs in
                Control.throw (Invalid_argument (Some msg))
            end
        end in
      go ty 1 args [] [].

  End Unsafe.
  End Constr.

  (** Type of the terms returned by [Builder.run builder val]. This type should be checked by unsafe
      combinators like [unsafe_constr] and [Ap.apply]. *)
  Ltac2 return_type (builder : 'a t) : constr := (builder ()).(type).

  (** A convenient shorthand for [Constr.subst_evars] *)
  Ltac2 subst_evars' (g : constr) : constr :=
    Option.default g (Constr.subst_evars g).

  Ltac2 map
    (fty : constr -> constr)
    (fval : constr -> ('a -> constr) -> 'b -> constr)
    (build : 'a t) : 'b t :=
    fun () =>
      let {type; build} := build () in
      let ty' := fty type in
      { type := ty';
        build := fun x => fval type build x }.

  #[local]
  Ltac2 instantiate_type fn (fixed_args : arg list) (other_args : arg list) :=
    let fty := Constr.type fn in
    let all_args := List.append fixed_args other_args in
    Control.with_holes
      (fun () =>
         error_context!
           [ fprintf "Error when checking argument types" ;
             fprintf "function:  %a" (pp_hovbox 2 pp_constr) fn ;
             fprintf "type:      %a" (pp_hovbox 2 pp_constr) fty ;
             fprintf "arguments: %a" (pp_hbox (pp_lines Arg.pp_typed)) all_args ]
           Constr.Unsafe.instantiate_prod fty all_args)
      (fun (args, ty) =>
         let args := List.map (Arg.map subst_evars') args in
         let ty := subst_evars' ty in
         let lazy_app () :=
           let args := List.map Arg.term args in
           Unsafe.make_app_list fn args in
         (lazy_app, ty)).

  (** This module allows one to combine builders in an applicative style. With a Galina function [f]
      and n builders [build_a1] .. [build_an], one can use [f] to combine the result of the n
      builders as follows:
      <<
        Ap.apply f fixed_args
          (Ap.arg_on prj1 build_a1)
          ...
          (Ap.arg_on prjn build_an)
          Ap.done
      >>

      The result is ['b Builder.t] if each projection [prji] has type ['b -> 'ai] and each builder
      [build_ai] has type ['ai Builder.t]. The Galina type returned by the resulting builder is
      calculated by specializing the function type of [f] with the type of each argument it is
      given. [fixed_args] is a [arg list], a list of terms or (optionally typed) wildcards which will be
      used as the first few arguments given to [f].

      The resulting builder will apply [cbv] on the resulting term.

      As an example, one may want to use the interface to create a builder which takes a (Ltac2)
      pair of lists of integers and return their concatenation as a Galina term:
      <<
        let build_int_list := build_list build_Z in
        Ap.apply '(@List.app) [Wildcard]
          (Ap.arg_on fst build_int_list)
          (Ap.arg_on snd build_int_list)
          Ap.done
      >>

      The result has type [(int list * int list) Builder.t].

      Exceptions:
        When defining a compound builder using the [Ap] interface, if the builders combined using
        [Ap.arg_on] are type correct (i.e. they produce terms of the type advertised by
        [return_type]), the compound builder can fail the first time it is run if the return type of
        each of the combined builders do not match the type signature of the Gallina function [f].

        When combining builders which do not do proper error checking, each call of the compound
        builder may fail with a type error blaming the function application rather than the input of
        the unsafe builder.

      Limitation:
        The builders one can create with the interface [Ap] are limited to the builders calling
        other builders and combining the results using a Galina function. *)
  Module Ap.

    Ltac2 Type ('b, 't, 'e) acc :=
      { ret : constr list -> ('b -> constr list) -> 't ;
        r_type : constr list ;
        r_term : 'b -> constr list }.

    (** Implementation *)
    #[local]
    Ltac2 insert (f  : 'b -> 'a) (builder : 'a t) : ('b, 't, 'e) acc -> ('b, 't, 'e) acc :=
      fun { ret; r_type; r_term } =>
      let { type; build } := builder () in
      { ret ;
        r_type := (type :: r_type) ;
        r_term := fun b => build (f b) :: r_term b
      }.

    (** Starter *)
    Ltac2 apply (fn : constr) (args : arg list)
        (x : ('b, 'b impl, 'e) acc -> 'r) : 'r :=
      let wild_ty ty := WildcardWithType ty in
      let term trm   := Term trm in
      let inst_ty xs :=
        error_context! [fprintf "Builder.Ap.apply"]
        instantiate_type fn args xs in
      let mk_app xs :=
        let (fn_app, _) := inst_ty (List.map term xs) in
        let trm := fn_app () in
        Std.eval_cbv RedFlags.all trm in
      let compile build_ty build_trm :=
        let build_ty := List.rev build_ty in
        let (_, type)    := inst_ty (List.map wild_ty build_ty) in
        let build args :=
          let args := build_trm args in
          let args := List.rev args in
          mk_app args in
        { type; build } in
      let acc :=
        { ret  := compile ;
          r_type := [] ;
          r_term := fun _ => [] } in
      x acc.


    (** Combinators *)
    Ltac2 arg_on (f  : 'b -> 'a) (builder : 'a t)
      (prev : ('b, 't, 'e) acc) :
      ( ('b, 't, 'e) acc -> 'r ) -> 'r :=
      fun k =>
        k (insert f builder prev).

    Ltac2 arg (builder : 'a t) := arg_on (fun x => x) builder.

    (** Finishers *)
    Ltac2 done (x : ('b, 't, 'e) acc) : 't :=
      let { ret    := compile ;
            r_type := x_ty  ;
            r_term := x_build }  := x in
      compile x_ty x_build.

  End Ap.

  Ltac2 build_pos : int Builder.t :=
    fun () =>
      { type := '(BinNums.positive);
        build := Int.as_pos }.

  Ltac2 build_N : int Builder.t :=
    fun () =>
      { type := '(BinNums.N);
        build := fun n =>
            if Int.lt n 0 then
              let msg := fprintf "numbers of type %t cannot be negative: %i" '(BinNums.N) n in
              Control.throw (Invalid_argument (Some msg))
            else if Int.lt 0 n then
              let n := (build_pos ()).(build) n in
              '(BinNums.Zpos $n)
            else
              '(BinNums.Z0) }.

  Ltac2 build_Z : int Builder.t :=
    fun () =>
      { type := '(BinNums.Z);
        build := fun n =>
            if Int.lt n 0 then
              let n := (build_pos ()).(build) (Int.neg n) in
              '(BinNums.Zneg $n)
            else if Int.lt 0 n then
              let n := (build_pos ()).(build) n in
              '(BinNums.Zpos $n)
            else
              '(BinNums.Z0) }.

  Ltac2 build_nat : int Builder.t :=
    fun () =>
      { type := '(nat);
        build := fun n =>
            if Int.lt n 0 then
              let msg := fprintf "numbers of type %t cannot be negative: %i" '(nat) n in
              Control.throw (Invalid_argument (Some msg))
            else Int.as_nat n }.

  Ltac2 make_list (ty : constr) (xs : constr list) : constr :=
    let cons := '(@cons) in
    let make_cons x xs := Unsafe.make_app3 cons ty x xs in
    List.foldr make_cons xs (Unsafe.make_app1 '(@nil) ty).

  Ltac2 make_pair tyA tyB := Unsafe.make_app2 '(@pair $tyA $tyB).

  Ltac2 make_bool (b : bool) : constr :=
    if b then '(true) else '(false).

  Ltac2 build_bool : bool Builder.t :=
  fun () =>
    { type := '(bool)  ;
      build := make_bool }.

  Ltac2 build_option (build : 'a Builder.t) : 'a option Builder.t :=
    fun () =>
      let {type; build} := build () in
      { type  := '(option $type);
        build := fun x =>
          match x with
          | None => '(@None $type)
          | Some x =>
              let x := build x in
              '(@Some $type $x)
          end }.

  Ltac2 build_list (build : 'a t) : 'a list t :=
    fun () =>
      let {type; build} := build () in
      { type  := constr:(list $type);
        build := fun x =>
          make_list type (List.map build x) }.

  Ltac2 build_pair (build_a : 'a t) (build_b : 'b t) : ('a * 'b) t :=
    fun () =>
    let {type := ty_a; build := build_a} := build_a () in
    let {type := ty_b; build := build_b} := build_b () in
    let pair_ty := constr:(($ty_a * $ty_b)%type) in
    { type := pair_ty;
      build := fun (a, b) =>
        let a := build_a a in
        let b := build_b b in
        constr:(($a, $b)) }.

  (** Requires [skylabs.prelude.pstring_string] which we can't import. *)
  Ltac2 build_stdlib_string : string t :=
    fun () =>
      { type  := '(String.string);
        build := String.to_string_constr }.

  Ltac2 build_pstring : string t :=
    fun () =>
    { type  := constr:(PrimString.string);
      build := Unsafe.make_string }.

  (** This creates a term builder which can be applied to any [constr] but applying it to a constr
      of a different type than [type] will result in a run-time exception. *)
  Ltac2 unsafe_constr (type : constr) : constr t :=
    fun () =>
      {type;
       build := fun x =>
         error_context!
           [ fprintf "constr builder for type %t" type;
             fprintf "invalid argument: %t" x ]
         constr:($x :> $type) }.

  Ltac2 run (builder : 'a t) (x : 'a) : constr :=
    (builder ()).(build) x.

  Ltac2 to_ltac1 (builder : 'a t) (x : 'a) : Ltac1.t :=
    Ltac1.of_constr ((builder ()).(build) x).

  Section example.

    Open Scope list_scope.
    Import Lists.List.ListNotations.

    Ltac2 from_lists (build_a : 'a Builder.t) (build_b : 'b Builder.t) () :=
      Ap.apply '(fun a b c => ([a] ++ [b] ++ List.rev c)%list) []
         (Ap.arg_on (fun (a,_,_) => a) build_a)
         (Ap.arg_on (fun (_,_,c) => c) build_a)
         (Ap.arg_on (fun (_,b,_) => b) build_b)
         Ap.done.

    Goal True.
      let builder := from_lists (constr '(nat)) (build_list build_nat) in
      let trm     := run builder ( '(1), [2;3;4], '(5)) in
      Control.assert_true (Constr.equal trm '([1;5;4;3;2])).
    Abort.

  End example.
End Builder.
