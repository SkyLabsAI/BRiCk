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
     Constr.Binder.type binder_i] for levels [1 <= i <= N].

     Levels can be handy because they are stable under extensions to an
     environment, unlike de Bruijn indices. *)

  Import Ltac2 Init Printf.

  Ltac2 Type rel_decl := Constr.Unsafe.RelDecl.t.

  Ltac2 Type t := {
    decls : rel_decl list; (** backwards *)

    (** The following are redundant, but speed up some operations. *)
    length : int; (** [= |decls|] *)
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
  Ltac2 empty : t := { decls := []; length := 0; rels := [] }.

  (** The number of declarations in an environment. *)
  Ltac2 length (env : t) : int := env.(length).

  (** Level of and reference to any next declaration added to environment
      [env]. (The reference is [Rel (|env|+1)]). *)
  Ltac2 next_level_int (env : t) : int := Int.add (env.(length)) 1.
  Ltac2 next_level_rel (env : t) : constr :=
    Constr.Unsafe.make_rel (next_level_int env).

  (**
  An environment's _level substitution_ sends references based on de
  Bruijn indices [Rel 1; ...; Rel (|env|+1)] to those based on levels
  [Rel (|env|+1); ...; Rel 1]. (It also sends levels to indices.)

  Used both to start working with de Bruijn levels, and to tidy up
  afterwards.

  Note: The variant [level_subst'] represents the substitution as a
  list of [Rel]s. It behaves identically to the learner's [fun (env :
  constr list) => subst_levels_to_indices (List.length env)] except
  that this version takes constant time.
  *)
  Ltac2 level_subst' (env : t) : constr list := env.(rels).
  Ltac2 level_subst (env : t) : constr -> constr :=
    Constr.Unsafe.substnl (env.(rels)) 0.

  (**
  Extend environment [env] with innermost declaration [level_subst env
  <$> decl].

  (Presupposes [decl] uses de Bruijn levels, not indices.)
  *)
  Ltac2 add_decl_level (env : t) (decl : rel_decl) : t :=
    let level := next_level_int env in
    let rels := env.(rels) in
    let decls := decl :: (env.(decls)) in
    let rels := Constr.Unsafe.make_rel level :: rels in
    { decls := decls; length := level; rels := rels }.

  (**
  Extend environment [env] with innermost declaration [level_subst env
  <$> decl].

  (Presupposes [decl] uses de Bruijn indices, not levels.)
  *)
  Ltac2 add_decl (env : t) (decl : rel_decl) : t :=
    let rels := env.(rels) in
    let mapper := Constr.Unsafe.substnl rels 0 in
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

  (** Pretty-printing *)
  Ltac2 pp : t pp := fun _ env =>
    let folder decl (acc : int * message list) :=
      let (level, msgs) := acc in
      let pp_decl := Constr.Unsafe.RelDecl.pp in
      let msgs := fprintf "%i : %a" level pp_decl decl :: msgs in
      let level := Int.sub level 1 in
      (level, msgs)
    in
    let (_, msgs) := foldr folder env (length env,[]) in
    pp_list pp_message () msgs.

  Ltac2 pp_named : t pp := fun _ env =>
    let folder decl (acc :
        int * Fresh.Free.t * ident list * constr list * message list) :=
      let (level, free, names, subs, msgs) := acc in
      let (free, name) := Fresh.for_rel_decl free decl in
      let fresh := Fresh.Free.union (Fresh.Free.of_ids [name]) free in
      let decl := Constr.Unsafe.RelDecl.map_name (fun _ => Some name) decl in
      let decl :=
        Constr.Unsafe.RelDecl.map_constr
          (Constr.Unsafe.substnl (List.rev subs) 0) decl
      in
      let pp_decl := Constr.Unsafe.RelDecl.pp in
      let msgs := fprintf "%i : %a" level pp_decl decl :: msgs in
      let level := Int.add level 1 in
      let names := name :: names in
      let subs := Constr.Unsafe.make_var name :: subs in
      (level, fresh, names, subs, msgs)
    in
    let (_, _, _, _, msgs) :=
      foldl folder env (1, Fresh.Free.of_goal(), [], [], [])
    in
    pp_list pp_message () (List.rev msgs).

  (**
  Low-level function to convert an environment to (i) a list of
  declarations sorted by level (switching inter-declaration references
  from de Bruijn levels to the terms obtained from [f level]) and (ii)
  the list of terms [f i | 1 <= i <= |env|]. The function [f] gets
  applied once per level, in order.

  Examples: [LevelEnv.to_list] and [LevelEnv.new_goal].
  *)

  Ltac2 close (f : int -> constr) (env : t) : constr list * rel_decl list :=
    let folder decl (acc : int * constr list * rel_decl list) :=
      let (level, refs, decls) := acc in
      let mapper := Constr.Unsafe.substnl refs 0 in
      let decl := Constr.Unsafe.RelDecl.map_constr mapper decl in
      let decls := decl :: decls in
      let refs := f level :: refs in
      let level := Int.add level 1 in
      (level, refs, decls)
    in
    let (_, refs, decls) := foldl folder env (1, [], []) in
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
    let decls := to_list env in
    let c := level_subst env c in
    let c := List.foldr folder decls c in
    c.

  (**
  Convert [env |- c] to the term [λ (x1 : t1) ... (xn : tn),
  level_subst env c] (switching from de Bruijn levels to indices),
  where the [x_i : t_i] are the envirnment's entries.
  *)

  Ltac2 add_funs (env : t) (c : constr) : constr :=
    let folder (decl : rel_decl) (acc : constr) :=
      match decl with
      | Constr.Unsafe.RelDecl.Assum b => Constr.Unsafe.make_lambda b acc
      | Constr.Unsafe.RelDecl.Def b v => Constr.Unsafe.make_let_in b v acc
      end
    in
    let decls := to_list env in
    let c := level_subst env c in
    let c := List.foldr folder decls c in
    c.


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
      match decl with
      | Constr.Unsafe.RelDecl.Assum b =>
          let decl :=
            Constr.Unsafe.RelDecl.Assum
              (Constr.Binder.map_type
               (Constr.Unsafe.substnl (List.rev subs) 0) b)
          in
          let env :=  add_decl env decl in
          let subs :=
            Constr.Unsafe.make_rel 1 :: List.map (Misc.liftn 1 1) subs
          in
          (env, subs)
      | Constr.Unsafe.RelDecl.Def _ v =>
          let v := Constr.Unsafe.substnl (List.rev subs) 0 v in
          let subs := v :: subs in
          (env, subs)
      end
    in
    let (env, subs) := foldl folder env (empty, []) in
    (env, List.rev_map (LevelEnv.level_subst env) subs).


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
      let intro_hyp (level : int) : constr :=
        let id := Array.get ids (Int.sub level 1) in
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
