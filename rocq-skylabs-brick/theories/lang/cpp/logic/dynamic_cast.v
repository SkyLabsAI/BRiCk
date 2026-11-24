(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(** * The result of a <<dynamic_cast>> to a class pointer or reference

    [dyncast mdc target] reads [expr.dynamic.cast]/9
    (<https://eel.is/c++draft/expr.dynamic.cast#9>) for an operand of class
    type whose object is reached by [mdc = [M; ...; src]] (from [derivationR];
    [M] is the class of the most-derived object, [src] the static class of the
    operand). Virtual bases are not supported (cpp2v rejects them), so every
    subobject is reached by exactly one path of direct bases.

    The rules for <<dynamic_cast>> are in [logic/expr.v].
 *)
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.lang.cpp.logic.pred.
Require Import skylabs.lang.cpp.logic.dispatch.

#[local] Open Scope list_scope.

Section dyncast.
  Context {σ : genv}.
  (** The classes are looked up in [tu]: [dyncast] instantiates it with the
      whole program ([genv_tu σ]); [tu_dyncast_ok] relates it to smaller [tu]s
      for computation. *)
  Variable tu : translation_unit.

  (** [public_path derived path] holds when every step of the path
      [derived :: path] of direct bases is a public base
      ([s_nonpublic_bases]). [None] if a class is not a known <<struct>>. *)
  Fixpoint public_path (derived : globname) (path : list globname) : option bool :=
    match path with
    | [] => Some true
    | base :: rest =>
        match tu.(types) !! derived with
        | Some (Gstruct st) =>
            andb (bool_decide (base ∉ st.(s_nonpublic_bases))) <$> public_path base rest
        | _ => None
        end
    end.

  (** [base_paths fuel cls] lists the paths [path] (as in
      [derived_to_base cls path]) to every base class subobject of [cls],
      direct or indirect. [None] if a class is not a known <<struct>> or [fuel]
      (the height of the hierarchy) runs out. *)
  Fixpoint base_paths (fuel : nat) (cls : globname) : option (list (list globname)) :=
    match fuel with
    | 0 => None
    | S fuel =>
        match tu.(types) !! cls with
        | Some (Gstruct st) =>
            (fun pss => List.concat pss) <$> mapM (fun '(base, _) =>
              (fun paths => [base] :: (cons base <$> paths)) <$> base_paths fuel base)
              st.(s_bases)
        | _ => None
        end
    end.

  (** [expr.dynamic.cast]/9.2: [v] (at [M :: v_path]) is a public base class
      subobject of the most-derived object, and [M] has exactly one base class
      subobject of class [target], which is public. The number of classes
      bounds the height of the hierarchy. *)
  Definition dyncast_cross (most_derived : globname) (v_path : list globname)
      (target : globname) : option (option offset) :=
    public_path most_derived v_path ≫= fun v_public =>
    base_paths (NM.cardinal tu.(types)) most_derived ≫= fun paths =>
    match List.filter (fun path => bool_decide (last path = Some target)) paths with
    | [c_path] =>
        public_path most_derived c_path ≫= fun c_public =>
        Some (if v_public && c_public
              then Some (base_to_derived most_derived v_path ,, derived_to_base most_derived c_path)
              else None)
    | _ => Some None
    end.

  (** [dyncast_in mdc target]:
      - [Some (Some off)]: the cast succeeds; the result is the operand's
        pointer offset by [off];
      - [Some None]: the cast fails (null pointer, or <<std::bad_cast>>);
      - [None]: undetermined (unknown class, [mdc = []]).

      [expr.dynamic.cast]/9.1: [v] is a public base class subobject of a
      [target] object, and only one [target] object is derived from [v]. With
      non-virtual bases, the objects derived from [v] are those along [mdc];
      [target] occurs at most once in [mdc], as no class is its own base. *)
  Definition dyncast_in (mdc : list globname) (target : globname) : option (option offset) :=
    match mdc with
    | [] => None
    | most_derived :: v_path =>
        match list_find (fun cls => cls = target) mdc with
        | Some (i, _) =>
            let below := drop (S i) mdc in
            public_path target below ≫= fun is_public : bool =>
            if is_public then Some (Some (base_to_derived target below))
            else dyncast_cross most_derived v_path target
        | None => dyncast_cross most_derived v_path target
        end
    end.
End dyncast.

(** [dyncast] is [dyncast_in] on the whole program. *)
Definition dyncast {σ : genv} : list globname -> globname -> option (option offset) :=
  dyncast_in σ.(genv_tu).

(** ** Computing [dyncast] from a translation unit *)
Section tu_dyncast.
  Context {σ : genv} (tu : translation_unit) (MOD : tu ⊧ σ).
  #[local] Set Default Proof Using "MOD".

  #[local] Lemma lookup_struct_ok cls st :
    tu.(types) !! cls = Some (Gstruct st) -> σ.(genv_tu).(types) !! cls = Some (Gstruct st).
  Proof. exact: glob_def_genv_compat_struct. Qed.

  #[local] Lemma public_path_ok derived path b :
    public_path tu derived path = Some b -> public_path σ.(genv_tu) derived path = Some b.
  Proof.
    elim: path derived b => [//|base rest IH] derived b /=.
    case Hd: (tu.(types) !! derived) => [[]|] //.
    rewrite (lookup_struct_ok _ _ Hd).
    case Hr: (public_path tu base rest) => [b'|] //= [<-].
    by rewrite (IH _ _ Hr).
  Qed.

  #[local] Lemma base_paths_ok fuel fuel' cls paths :
    fuel <= fuel' ->
    base_paths tu fuel cls = Some paths -> base_paths σ.(genv_tu) fuel' cls = Some paths.
  Proof.
    elim: fuel fuel' cls paths => [//|fuel IH] [|fuel'] cls paths /= Hle; first lia.
    case Hd: (tu.(types) !! cls) => [gd|] //. case: gd Hd => // st Hd.
    rewrite (lookup_struct_ok _ _ Hd).
    case Hm: (mapM _ _) => [pss|] //= [<-].
    erewrite mapM_Some_2; first done.
    apply mapM_Some_1 in Hm. eapply Forall2_impl; first exact Hm.
    move=> [base li] ps /=. case Hb: (base_paths tu fuel base) => [ps'|] //= [<-].
    by rewrite (IH fuel' base ps' ltac:(lia) Hb).
  Qed.

  #[local] Lemma dyncast_cross_ok m v_path target r :
    dyncast_cross tu m v_path target = Some r ->
    dyncast_cross σ.(genv_tu) m v_path target = Some r.
  Proof.
    rewrite /dyncast_cross.
    case Hv: (public_path tu m v_path) => [v|] //=. rewrite (public_path_ok _ _ _ Hv) /=.
    case Hp: (base_paths tu _ m) => [paths|] //=.
    rewrite (base_paths_ok _ (NM.cardinal (types (genv_tu σ))) _ _ _ Hp) /=; last first.
    { apply type_table_le_cardinal, types_compat, genv_compat_submodule, MOD. }
    case: (List.filter _ paths) => [|c_path [|??]] //=.
    case Hc: (public_path tu m c_path) => [c|] //=. by rewrite (public_path_ok _ _ _ Hc).
  Qed.

  Lemma tu_dyncast_ok mdc target r :
    dyncast_in tu mdc target = Some r -> dyncast mdc target = Some r.
  Proof.
    rewrite /dyncast /dyncast_in. case: mdc => [//|m v_path].
    case: (list_find _ _) => [[i ?]|]; last exact: dyncast_cross_ok.
    case Hp: (public_path tu target _) => [[]|] //=; rewrite (public_path_ok _ _ _ Hp) //=.
    exact: dyncast_cross_ok.
  Qed.
End tu_dyncast.
