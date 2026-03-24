
Require Import skylabs.ltac2.extra.internal.init.
Require Import skylabs.ltac2.extra.internal.constr.
Require Import skylabs.ltac2.extra.internal.int.
Require Import skylabs.ltac2.extra.internal.list.
Require Import skylabs.ltac2.extra.internal.string.

Require Import Stdlib.Strings.PrimString.

(** ['a Builder.t] provides a function ['a -> constr] to turn an Ltac2 value into a Gallina term.
    Builders can be combined to build bigger builders. If one defines a Ltac2 type [foo] and a
    builder [build_foo] for it, one can use it to turn [xs : foo option list] into a term with
    [run (build_list (build_option build_foo)) xs]. *)
Module Builder.
  Import Ltac2 Init Constr.

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

  Ltac2 seq2 (fty : constr -> constr -> constr)
    (fval : constr ->
            ('a -> constr) ->
            constr ->
            ('b -> constr) ->
            'c -> constr)
    (build_a : 'a t) (build_b : 'b t) : 'c t :=
    fun () =>
      let {type := ty_a; build := build_a} := build_a () in
      let {type := ty_b; build := build_b} := build_b () in
      { type  := fty ty_a ty_b;
        build := fval ty_a build_a ty_b build_b }.

  Ltac2 seq3 (fty : constr -> constr -> constr -> constr)
    (fval : constr ->
            ('a -> constr) ->
            constr ->
            ('b -> constr) ->
            constr ->
            ('c -> constr) ->
            'd -> constr)
    (build_a : 'a t) (build_b : 'b t) (build_c : 'c t) : 'd t :=
    fun () =>
      let {type := ty_a; build := build_a} := build_a () in
      let {type := ty_b; build := build_b} := build_b () in
      let {type := ty_c; build := build_c} := build_c () in
      { type  := fty ty_a ty_b ty_c;
        build := fval ty_a build_a ty_b build_b ty_c build_c }.

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


  Ltac2 build_app1_with
    (fn : constr) (args : arg list)
    (f : 'b -> 'a)
    (build_a : 'a Builder.t) : 'b Builder.t :=
    fun () =>
    let inst_ty x := instantiate_type fn args [x] in
    Builder.map
      (fun ty =>
          snd (inst_ty (WildcardWithType ty)))
      (fun _ty_a build_a b =>
         let trm := build_a (f b) in
         let (fn_args, _ty_b) := inst_ty (Term trm) in
         let trm  := fn_args () in
         Std.eval_cbv RedFlags.all trm)
      build_a ().

  Ltac2 build_app2_with
    (fn : constr) (args : arg list)
    (f : 'c -> 'a * 'b)
    (build_a : 'a Builder.t)
    (build_b : 'b Builder.t)
    : 'c Builder.t :=
    fun () =>
    let inst_ty x y := instantiate_type fn args [x;y] in
    Builder.seq2
      (fun ty_a ty_b =>
          snd (inst_ty (WildcardWithType ty_a) (WildcardWithType ty_b)))
      (fun _ty_a build_a
         _ty_b build_b
         c =>
         let (a, b) := f c in
         let trm_a := build_a a in
         let trm_b := build_b b in
         let (fn_args, _ty_c) := inst_ty (Term trm_a) (Term trm_b) in
         let trm_c := fn_args () in
         Std.eval_cbv RedFlags.all trm_c)
      build_a build_b ().

  Ltac2 build_app3_with
    (fn : constr) (args : arg list)
    (f : 'd -> 'a * 'b * 'c)
    (build_a : 'a Builder.t)
    (build_b : 'b Builder.t)
    (build_c : 'c Builder.t)
    : 'd Builder.t :=
    fun () =>
    let inst_ty a b c :=
        instantiate_type fn args [a;b;c] in
    Builder.seq3
      (fun ty_a ty_b ty_c =>
         snd (inst_ty
                (WildcardWithType ty_a)
                (WildcardWithType ty_b)
                (WildcardWithType ty_c)))
      (fun _ty_a build_a
         _ty_b build_b
         _ty_c build_c
         d =>
         let (a, b, c) := f d in
         let trm_a := build_a a in
         let trm_b := build_b b in
         let trm_c := build_c c in
         let (fn_args, _ty_c) := inst_ty (Term trm_a) (Term trm_b) (Term trm_c) in
         let trm_c := fn_args () in
         Std.eval_cbv RedFlags.all trm_c)
      build_a build_b build_c ().

  Ltac2 build_app1
    (fn : constr) (args : arg list)
    (build_a : 'a Builder.t) : 'a Builder.t :=
    build_app1_with fn args (fun a => a) build_a.

  Ltac2 build_app2
    (fn : constr) (args : arg list)
    (build_a : 'a Builder.t)
    (build_b : 'b Builder.t)
    : ('a * 'b) Builder.t :=
    build_app2_with fn args (fun a => a) build_a build_b.

  Ltac2 build_app3
    (fn : constr) (args : arg list)
    (build_a : 'a Builder.t)
    (build_b : 'b Builder.t)
    (build_c : 'c Builder.t)
    : ('a * 'b * 'c) Builder.t :=
    build_app3_with fn args (fun a => a) build_a build_b build_c.

  Ltac2 build_pos : int Builder.t :=
    fun () =>
      { type := '(BinNums.positive);
        build := Int.as_pos }.


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

  Ltac2 constr (type : constr) : constr t :=
    fun () => {type; build := fun x => x}.

  Ltac2 run (builder : 'a t) (x : 'a) : constr :=
    (builder ()).(build) x.

  Ltac2 to_ltac1 (builder : 'a t) (x : 'a) : Ltac1.t :=
    Ltac1.of_constr ((builder ()).(build) x).

End Builder.
