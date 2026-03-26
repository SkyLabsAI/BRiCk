
Require Import skylabs.ltac2.extra.internal.init.
Require Import skylabs.ltac2.extra.internal.constr.
Require Import skylabs.ltac2.extra.internal.int.
Require Import skylabs.ltac2.extra.internal.list.
Require Import skylabs.ltac2.extra.internal.string.

Require Import Stdlib.Strings.PrimString.

Import Ltac2 Init.

Ltac2 Type ('a, 'r) cps_list :=
   [ CpsList(('a Init.list, 'r) cps) ].

(** Monad which helps build a list in CPS style *)
Module CpsList.
  Import Ltac2.

  Ltac2 run : ('a, 'r) cps_list -> 'a list :=
    fun (CpsList f_xs) => f_xs (fun xs => xs).

  Ltac2 run_with : ('a, 'r) cps_list -> ('a list -> 'r) -> 'r :=
    fun (CpsList f_xs) ret => f_xs ret.

  Ltac2 nil : ('a, 'r) cps_list :=
    CpsList (fun ret => ret []).

  Ltac2 ret (x : 'a) : ('a, 'r) cps_list :=
    CpsList (fun ret => ret [x]).

  Ltac2 cons (x : 'a) :
    ('a, 'r) cps_list -> ('a, 'r) cps_list :=
    fun (CpsList f_xs) =>
       CpsList (fun ret => f_xs (fun xs => ret (x :: xs)) ).

  Ltac2 list (xs : 'a list) : ('a, 'r) cps_list :=
    CpsList (fun ret => ret xs).

  Ltac2 app  :
    ('a, 'r) cps_list ->
    ('a, 'r) cps_list ->
    ('a, 'r) cps_list :=
    fun (CpsList f_xs) (CpsList f_ys) =>
       CpsList (fun ret =>
       f_xs (fun xs =>
       f_ys (fun ys =>
       ret (List.append xs ys)))).

  Ltac2 Eval run (cons 1 (cons 2 (cons 3 nil))).

  Ltac2 Eval run (app (list [1;2;3]) (list [4;5;6])).

End CpsList.


(** ['a Builder.t] provides a function ['a -> constr] to turn an Ltac2 value into a Gallina term.
    Builders can be combined to build bigger builders. If one defines a Ltac2 type [foo] and a
    builder [build_foo] for it, one can use it to turn [xs : foo option list] into a term with
    [run (build_list (build_option build_foo)) xs]. *)
Module Builder.
  Import Ltac2 Init Constr Printf.

  Ltac2 Type 'a impl := { type : constr; build : 'a -> constr }.
  Ltac2 Type 'a t := unit -> 'a impl.

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
    Control.with_holes
      (fun () => Unsafe.instantiate_prod fty (List.append fixed_args other_args))
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
        _apply f fixed_args
          (_arg_on prj1 build_a1)
          ...
          (_arg_on prjn build_an)
          _done
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
        _apply '(@List.app) [Wildcard]
          (_arg_on fst build_int_list)
          (_arg_on snd build_int_list)
          _done
      >>

      The result has type [(int list * int list) Builder.t].

      Limitation: the builders one can create with the interface [Ap] are limited to the builders
      calling other builders and combining the results using a Galina function. *)
  Module Ap.

    Ltac2 Type ('b, 't, 'e) acc :=
      { ret : constr list -> ('b -> constr list) -> 't ;
        r_type : (constr, 'e) cps_list ;
        r_term : 'b -> (constr, 'e) cps_list }.

    (** Implementation *)
    #[local]
    Ltac2 _insert (f  : 'b -> 'a) (builder : 'a t) : ('b, 't, 'e) acc -> ('b, 't, 'e) acc :=
      fun { ret; r_type; r_term } =>
      let { type; build } := builder () in
      { ret ;
        r_type := CpsList.cons type r_type ;
        r_term := fun b => CpsList.cons (build (f b)) (r_term b)
      }.

    (** Starter *)
    Ltac2 _apply (fn : constr) (args : arg list)
        (x : ('b, 't, 'e) acc -> 'r) : 'r :=
      let wild_ty ty := WildcardWithType ty in
      let term trm   := Term trm in
      let inst_ty xs := instantiate_type fn args xs in
      let mk_app xs :=
        let (fn_app, _) := inst_ty (List.map term xs) in
        let trm := fn_app () in
        Std.eval_cbv RedFlags.all trm in
      let compile build_ty build_trm :=
        let (_, type)    := inst_ty (List.map wild_ty build_ty) in
        let build args := mk_app (List.rev (build_trm args)) in
        { type; build } in
      let acc :=
        { ret  := compile ;
          r_type := CpsList.nil ;
          r_term := fun _ => CpsList.nil } in
      x acc.


    (** Combinators *)
    Ltac2 _arg_on (f  : 'b -> 'a) (builder : 'a t)
      (prev : ('b, 't, 'e) acc) :
      ( ('b, 't, 'e) acc -> 'r ) -> 'r :=
      fun k =>
        k (_insert f builder prev).

    Ltac2 _arg (builder : 'a t) := _arg_on (fun x => x) builder.

    (** Finishers *)
    Ltac2 _done (x : ('b, 't, 'e) acc) : 't :=
      let { ret    := compile ;
            r_type := x_ty  ;
            r_term := x_build }  := x in
      compile
        (CpsList.run x_ty)
        (fun b => CpsList.run (x_build b)).

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

  (** TODO: do type checking in [build] *)
  Ltac2 constr (type : constr) : constr t :=
    fun () => {type; build := fun x => x}.

  Ltac2 run (builder : 'a t) (x : 'a) : constr :=
    (builder ()).(build) x.

  Ltac2 to_ltac1 (builder : 'a t) (x : 'a) : Ltac1.t :=
    Ltac1.of_constr ((builder ()).(build) x).

  Section example.

    Import Ap.
    Open Scope list_scope.
    Import Lists.List.ListNotations.

    Ltac2 from_lists (build_a : 'a Builder.t) (build_b : 'b Builder.t) () :=
      _apply '(fun a b c => (a ++ List.rev b ++ c)%list) []
         (_arg_on (fun (a,_,_) => a) build_a)
         (_arg_on (fun (_,b,_) => b) build_b)
         (_arg_on (fun (_,_,c) => c) build_a)
         _done.

    Goal True.
      let builder := from_lists (constr '(list nat)) (build_list build_nat) in
      let trm     := run builder ( '([1]), [2;3;4], '([5])) in
      Control.assert_true (Constr.equal trm '([1;4;3;2;5])).
    Abort.

  End example.
End Builder.
