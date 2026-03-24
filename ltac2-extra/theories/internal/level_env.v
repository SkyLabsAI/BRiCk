(*
 * Copyright (C) 2022-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.plugin.
Require Import skylabs.ltac2.extra.internal.misc.
Require Import skylabs.ltac2.extra.internal.init.
Require Import skylabs.ltac2.extra.internal.constr.
Require Import skylabs.ltac2.extra.internal.list.
Require Import skylabs.ltac2.extra.internal.printf.
Require Import skylabs.ltac2.extra.internal.fresh.
Require Import skylabs.ltac2.extra.internal.control.
Require Import skylabs.ltac2.extra.internal.std.

(** Environments for de Bruijn levels. *)
Module LevelEnv.
  (* An environment for de Bruijn _levels_ is [decl1; ...; declN] where each
     declaration [decl_i] is either a local assumption [binder_i] or a local
     definition [binder_i := term_i]. Under an environment, [Rel i :
     Constr.Binder.type binder_i] for levels [offset < i <= offset + N].

     The default [offset] is [0]. Non-zero [offset]s are useful when working in
     stacked environments.

     Levels can be handy because they are stable under extensions to an
     environment, unlike de Bruijn indices. *)

  Import Ltac2 Init Printf.

  Ltac2 Type rel_decl := Constr.Unsafe.RelDecl.t.

  Ltac2 Type t := {
    decls : rel_decl list; (** backwards *)
    offset : int;

    (** The following are redundant, but speed up some operations. *)
    length : int; (** [= |decls|] *)
    (** NOTE: [Rel]s stored in [rels] are _relative_, not absolute, w.r.t. to
    [offset]. This is necessary to be able to use them in
    [substnl rels offset ..]. *)
    rels : constr list; (** [= [Rel |decls|; ...; Rel 1] *)
  }.

  (** Fold over an environment's declarations by level (from outermost to
      innermost). *)
  Ltac2 foldli (f : int -> rel_decl -> 'a -> 'a) (env : t) (acc : 'a) : 'a :=
    (** Tail recursive, just in case. *)
    let decls := List.rev (env.(decls)) in
    List.foldli f decls acc.
  Ltac2 foldl (f : rel_decl -> 'a -> 'a) (env : t) (acc : 'a) : 'a :=
    (** Tail recursive, just in case. *)
    let decls := List.rev (env.(decls)) in
    List.foldl f decls acc.

  (** Fold over an environment's declarations from right to left. *)
  Ltac2 foldr (f : rel_decl -> 'a -> 'a) (env : t) (acc : 'a) : 'a :=
    List.foldl f (env.(decls)) acc.

  (** The empty environment *)
  Ltac2 empty : t := { decls := []; offset := 0; length := 0; rels := [] }.

  Ltac2 empty_w_offset (offset : int) : t :=
    { empty with offset }.

  (** The number of declarations in an environment. *)
  Ltac2 length (env : t) : int := env.(length).

  (** The offset of an environment. *)
  Ltac2 offset (env : t) : int := env.(offset).

  (** Level of and reference to any next declaration added to environment
      [env]. (The reference is [Rel (|env|+1)]). *)
  Ltac2 next_level_int (env : t) : int := Int.add (env.(length)) 1.
  Ltac2 next_level_rel (env : t) : constr :=
    Constr.Unsafe.make_rel (next_level_int env).

  (**
  An environment's _level substitution_ sends references based on de
  Bruijn indices [Rel (offset+1); ...; Rel (offset+|env|+1)] to those based on levels
  [Rel (offset+|env|+1); ...; Rel (offset+1)]. (It also sends levels to indices.)

  Used both to start working with de Bruijn levels, and to tidy up
  afterwards.

  WARNING: Do not use [level_subst env c] if [c] has [Rel]s not bound by [env].
  It sends [Rel (k)] for [|env|+offset+1 < k] to [Rel(k-|env|-offset)], making
  them collide with [Rel]s bound by [env].

  If [c] has no such [Rel]s, then [level_subst env (level_subst env c) = c].

  See [level_subst_inv] for a version that is unconditionally involutive.
  *)
  Ltac2 level_subst' (env : t) : constr list := env.(rels).
  Ltac2 level_subst (env : t) : constr -> constr :=
    Constr.Unsafe.substnl (env.(rels)) (env.(offset)).

  (**
  [level_subst_inv env c] leaves [Rel]s above [offset+|env|] untouched and is
  always involutive, i.e. it satisfies [level_subst env (level_subst env c) =
  c].

  On [Rel]s bound by [env], [level_subst_inv env c] behaves exactly as
  [level_subst env c].
  *)
  Ltac2 level_subst_inv (env : t) (c : constr) : constr :=
    (* [substnl] assumes that we are instantiating binders and shifts [Rel]s
    above [env.(length)] accordingly. This would make [level_subst] not
    involutive. To fix this, we pre-emptively shift those binders by
    [env.(length)]. The shift is then undone by [substnl]. *)
    let n := env.(length) in
    let c := Constr.Unsafe.liftn n (Int.add n (Int.add (env.(offset)) 1)) c in
    Constr.Unsafe.substnl (env.(rels)) (env.(offset)) c.

  (**
  Extend environment [env] with innermost declaration [level_subst env
  <$> decl].

  (Presupposes [decl] uses de Bruijn levels, not indices.)
  *)
  Ltac2 add_decl_level (env : t) (decl : rel_decl) : t :=
    let length := next_level_int env in
    let rels := env.(rels) in
    let decls := decl :: (env.(decls)) in
    let rels := Constr.Unsafe.make_rel length :: rels in
    { env with decls; length; rels }.

  (**
  Extend environment [env] with innermost declaration [level_subst env
  <$> decl].

  (Presupposes [decl] uses de Bruijn indices, not levels.)
  *)
  Ltac2 add_decl (env : t) (decl : rel_decl) : t :=
    let rels := env.(rels) in
    let mapper := Constr.Unsafe.substnl rels (env.(offset)) in
    let decl := Constr.Unsafe.RelDecl.map_constr mapper decl in
    add_decl_level env decl.

  (**
  Nothing that follows needs to know the representation of
  environments.
  *)

  (** Add an assumption based on a binder *)
  Ltac2 add_binder_assum (env : t) (b : binder) : t :=
    add_decl env (Constr.Unsafe.RelDecl.Assum b).

  (** The same, for an array of binders. *)
  Ltac2 add_binder_assum_array (env : t) (bs : binder array) : t :=
    Array.fold_left add_binder_assum env bs.

  (** Add a local definition based on a binder *)
  Ltac2 add_binder_def (env : t) (b : binder) (val : term) : t :=
    add_decl env (Constr.Unsafe.RelDecl.Def b val).

  (**
     [cut env n] splits [env] into a prefix env [p_env] of length [n] and a
     suffix env [s_env] of length [|env| - n]. [s_env.(offset)] is [offset +
     n].

     The terms in [p_env] and [s_env] are unchanged, i.e. identical to those in
     [env].
   *)
  Ltac2 cut (env : t) (n : int) : t * t :=
    let _ := Control.assert_valid_argument "LevelEnv.cut" (Int.ge n 0) in
    let _ := Control.assert_valid_argument "LevelEnv.cut" (Int.lt n (env.(length))) in
    let s_len := Int.sub (env.(length)) n in
    let s_offset := Int.add (env.(offset)) n in
    let (s_decls, p_decls) := List.split_at s_len (env.(decls)) in
    let (s_rels, p_rels) := List.split_at s_len (env.(rels)) in
    let p_env := { decls := p_decls; rels := p_rels; length := n; offset := env.(offset) } in
    let s_env := { decls := s_decls; rels := s_rels; length := s_len; offset := s_offset } in
    (p_env, s_env).

  (** [append] is the inverse of [cut]. *)
  Ltac2 append (p_env : t) (s_env : t) : t :=
    let _ :=
      Control.assert_valid_argument "LevelEnv.append"
        (Int.equal (Int.add (p_env.(offset)) (p_env.(length))) (s_env.(offset)))
    in
    let length := Int.add (p_env.(length)) (s_env.(length)) in
    let rels := List.append (s_env.(rels)) (p_env.(rels)) in
    let decls := List.append (s_env.(decls)) (p_env.(decls)) in
    let offset := p_env.(offset) in
    { decls; offset; length; rels }.

  (** [skipn env n] drops the [n] highest levels from [env]. *)
  Ltac2 skipn (env : LevelEnv.t) (n : int) :=
    { env with
        decls := List.skipn n (env.(decls));
        length := Int.sub (env.(length)) n;
        rels := List.skipn n (env.(rels))
    }.

  (** [by_level env i] returns the [i]th entry where [i] is interpreted as an
      absolute level, i.e. [i] must include [offset].
    *)
  Ltac2 by_level (env : LevelEnv.t) (i : int) : Constr.Unsafe.RelDecl.t :=
    List.nth (env.(decls))
      (Int.sub (LevelEnv.length env) (Int.add (Int.sub i (env.(offset))) 1)).

  (** [to_level_array env] represents [env] as zero-indexed array in level order. *)
  Ltac2 to_level_array (env : LevelEnv.t) : Constr.Unsafe.RelDecl.t array :=
    let arr :=
      Array.make (LevelEnv.length env)
        (Constr.Unsafe.RelDecl.Assum (Constr.Binder.make None 'False)) in
    let () := LevelEnv.foldli (fun i rd () => Array.set arr i rd) env () in
    arr.

  (** Pretty-printing *)
  Ltac2 pp : t pp := fun _ env =>
    let folder decl (acc : int * message list) :=
      let (level, msgs) := acc in
      let pp_decl := Constr.Unsafe.RelDecl.pp in
      let msgs := fprintf "%i : %a" level pp_decl decl :: msgs in
      let level := Int.sub level 1 in
      (level, msgs)
    in
    let (_, msgs) := foldr folder env (Int.add (env.(offset)) (env.(length)),[]) in
    pp_list pp_message () (msgs).

  Ltac2 pp_named : t pp := fun _ env =>
    let folder decl (acc :
        int * Fresh.Free.t * ident list * constr list * message list) :=
      let (level, free, names, subs, msgs) := acc in
      let (free, name) := Fresh.for_rel_decl free decl in
      let fresh := Fresh.Free.union (Fresh.Free.of_ids [name]) free in
      let decl := Constr.Unsafe.RelDecl.map_name (fun _ => Some name) decl in
      let decl :=
        Constr.Unsafe.RelDecl.map_constr
          (Constr.Unsafe.substnl (List.rev subs) (env.(offset))) decl
      in
      let pp_decl := Constr.Unsafe.RelDecl.pp in
      let msgs := fprintf "%i : %a" level pp_decl decl :: msgs in
      let level := Int.add level 1 in
      let names := name :: names in
      let subs := Constr.Unsafe.make_var name :: subs in
      (level, fresh, names, subs, msgs)
    in
    let (_, _, _, _, msgs) :=
      foldl folder env (Int.add (env.(offset)) 1, Fresh.Free.of_goal(), [], [], [])
    in
    pp_list pp_message () (List.rev msgs).


  (** [named_subst env c] computes named binders for [env] and substitutes them
  into [c]. *)
  Ltac2 named_subst (env : t) : constr -> constr :=
   let (_, ls) :=
      let fn rd (free, ls) :=
        let (free, id) := Fresh.for_rel_decl free rd in
        (free, Constr.Unsafe.make_var id :: ls)
      in
      LevelEnv.foldr fn env (Fresh.Free.of_goal (), [])
    in
    Constr.Unsafe.substnl ls (env.(offset)).

  (**
  Low-level function to convert an environment to (i) a list of
  declarations sorted by level (switching inter-declaration references
  from de Bruijn levels to the terms obtained from [f level]) and (ii)
  the list of terms [f i | offset < i <= offset+|env|]. The function [f] gets
  applied once per level, in order.

  Examples: [LevelEnv.to_list] and [LevelEnv.new_goal].
  *)

  Ltac2 close (f : int -> constr) (env : t) : constr list * rel_decl list :=
    let folder decl (acc : int * constr list * rel_decl list) :=
      let (level, refs, decls) := acc in
      let mapper c :=
        let c := Constr.Unsafe.liftn (Int.sub level 1) level c in
        Constr.Unsafe.substnl refs (env.(offset)) c
      in
      let decl := Constr.Unsafe.RelDecl.map_constr mapper decl in
      let decls := decl :: decls in
      let refs := f level :: refs in
      let level := Int.add level 1 in
      (level, refs, decls)
    in
    let (_, refs, decls) := foldl folder env (Int.add (env.(offset)) 1, [], []) in
    let refs := List.rev refs in
    let decls := List.rev decls in
    (refs, decls).

  (**
  Convert an environment to a list of declarations sorted by level
  (switching from de Bruijn levels to indices).

  Used to tidy up after working with de Bruijn levels.

  Note: Behaves similarly to the learner's [fun (env : constr list) =>
  env_levels_to_indices (List.rev env) : constr list], except that
  this version includes names and local definitions, is tail
  recursive, and takes only linear time (in the number of declarations
  and the size of their values and types).
  *)
  Ltac2 to_list (env : t) : rel_decl list :=
    let (_, decls) := close Constr.Unsafe.make_rel env in
    decls.

  (**
  Deconstruct a term of the form [∀ (x1 : t1) ... (xN : tN), c] into
  the environment [env := [x1 : t1; ...; xN : tN]] and term
  [level_subst env c] (switching from de Bruijn indices to levels).
  *)

  Ltac2 strip_universals (env : t) (c : constr) : t * constr :=
    let rec go env c :=
      let k := Constr.Unsafe.kind c in
      match k with
      | Constr.Unsafe.LetIn b c1 c2 => go (add_binder_def env b c1) c2
      | Constr.Unsafe.Prod b c => go (add_binder_assum env b) c
      | _ => (env, level_subst env c)
      end
    in
    go env c.


  (**
  Convert [env |- c] to the term [f (x1 : t1 [:= v1]) $ .. $ f (xn : tn [:=
  vn]), level_subst env c] (switching from de Bruijn levels to indices), where
  the [x_i : t_i] are the envirnment's entries.
  *)
  Ltac2 to_constr
    (f : Constr.Unsafe.RelDecl.t -> constr -> constr)
    (env : t)
    (c : constr) : constr :=
    let decls := to_list env in
    let c := level_subst env c in
    let c := List.foldr f decls c in
    c.

  (**
  Convert [env |- c] to the term [∀ (x1 : t1) ... (xn : tn),
  level_subst env c] (switching from de Bruijn levels to indices),
  where the [x_i : t_i] are the envirnment's entries.
  *)

  Ltac2 add_universals (env : t) (c : constr) : constr :=
    let folder (decl : rel_decl) (acc : constr) :=
      match decl with
      | Constr.Unsafe.RelDecl.Assum b => Constr.Unsafe.make_prod b acc
      | Constr.Unsafe.RelDecl.Def b v => Constr.Unsafe.make_let_in b v acc
      end
    in
    to_constr folder env c.

  (**
  Convert [env |- c] to the term [λ (x1 : t1) ... (xn : tn),
  level_subst env c] (switching from de Bruijn levels to indices),
  where the [x_i : t_i] are the environment's entries.
  *)

  Ltac2 add_funs (env : t) (c : constr) : constr :=
    let folder (decl : rel_decl) (acc : constr) :=
      match decl with
      | Constr.Unsafe.RelDecl.Assum b => Constr.Unsafe.make_lambda b acc
      | Constr.Unsafe.RelDecl.Def b v => Constr.Unsafe.make_let_in b v acc
      end
    in
    to_constr folder env c.


  (**
  Convert an environment [env := [x1 : t1 := ?b1; ...; xn : tn := ?bn]]
  into an environment [y1 : ti; ...; yk : tk] such that
  - for all [0 < i < k] there exist a [0 < j < n] such that
    * [xj] such that [xj] is the [i]th [Assum] in [env]
    * [yi] is [xj]
    * [ti] is [tj] where every de-Bruin level [k < j] pointing to a preceding
      [Def] in [env] has been substituted with the corresponding body [bk],
      and all other indices have been adjusted to account for the dropped
      [Def]s
  Also return the substitution used in the binders [tj]. It can be applied
  to a term using de-Bruijn _levels_ to transport it to the new environment.
  *)
  Ltac2 substitute_defs (env : t) : t * constr list :=
    (* We need to traverse [env] from the outermost decl to the innermost *)
    let folder (decl : rel_decl) (env, subs) :=
      let f := Constr.Unsafe.substnl (List.rev subs) (env.(offset)) in
      match decl with
      | Constr.Unsafe.RelDecl.Assum b =>
          let decl :=
            Constr.Unsafe.RelDecl.Assum (Constr.Binder.map_type f b)
          in
          let env := add_decl env decl in
          let subs :=
            Constr.Unsafe.make_rel 1
              :: List.map (Misc.liftn 1 1) subs
          in
          (env, subs)
      | Constr.Unsafe.RelDecl.Def _ v =>
          let subs := f v :: subs in
          (env, subs)
      end
    in
    let (env, subs) := foldl folder env (empty_w_offset (env.(offset)), []) in
    let f c :=
      Constr.Unsafe.substnl (env.(rels)) 0 c
    in
    (env, List.rev_map f subs).


  (**
  Convert environment [x1 : t1; ...; xn : tn] into an array of fresh
  identifiers [|x'1; ...; x'n|] based on the [x_i].
  *)
  Ltac2 fresh_ident_array (free : Fresh.Free.t) (env : t) :
      Fresh.Free.t * ident array :=
    let n := length env in
    let ids := Array.make n ident:(dummy) in
    let folder (decl : rel_decl) (acc : int * Fresh.Free.t) :=
      let (i, free) := acc in
      let (free, id) := Fresh.for_rel_decl free decl in
      Array.set ids i id;
      (Int.add i 1, free)
    in
    let (_, free) := foldl folder env (0,free) in
    (free, ids).

  (**
  Given [x1 : ty_1; ...; xn : ty_n |- c], extend Coq's proof state
  with a new last goal:

  <<
    hyp_1 : ty_1
    hyp_2 : [hyp_1/Rel 1]ty_2
    ...
    hyp_n : [hyp_i/Rel i | 1 <= i < n]ty_n
    ---------------------------------------
    [hyp_i/Rel i | 1 <= i <= n]c =: c'
  >>

  (switching from de Bruijn levels to hypotheses) where the [hyp_i]
  have fresh names based on the [x_i]. Then, focus on that new goal,
  and invoke continuation [cnt] with identifiers [hyp_1; ...; hyp_n],
  hypotheses [Var hyp_1; ...; Var hyp_n] and term [c'].
  *)
  Ltac2 new_goal (free : Fresh.Free.t) (env : t) (c : constr)
      (cnt : Fresh.Free.t -> ident list -> constr list -> constr -> unit) :
      (evar * constr array) :=
    let (free, ids) := fresh_ident_array free env in
    let forall_c := add_universals env c in
    Control.focus_new_goal forall_c (fun () =>
      let offset1 := Int.add (env.(offset)) 1 in
      let intro_hyp (level : int) : constr :=
        let id := Array.get ids (Int.sub level offset1) in
        let () := Std.intro_nobacktrack (Some id) (Some Std.MoveLast) in
        Constr.Unsafe.make_var id
      in
      let (hyps, _) := close intro_hyp env in
      (** There's no need to substitute in [c] again. *)
      let c := Control.goal() in
      cnt free (Array.to_list ids) hyps c
    ).

  Ltac2 @ external make_evar_in_level_env_ocaml :
     bool -> bool -> rel_decl list -> constr -> evar * constr array :=
    "ltac2_extensions" "make_evar_in_level_env".

  Ltac2 make_evar_in_level_env (tc_cand : bool) (env : t) (ty : constr) :=
    make_evar_in_level_env_ocaml false tc_cand (env.(decls)) ty.

  Ltac2 make_evar_in_level_env_no_goal (tc_cand : bool) (env : t) (ty : constr) :=
    make_evar_in_level_env_ocaml true tc_cand (env.(decls)) ty.

End LevelEnv.
