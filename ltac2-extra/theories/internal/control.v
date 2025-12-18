(*
 * Copyright (C) 2022-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import skylabs.ltac2.extra.internal.init.
Require Import skylabs.ltac2.extra.internal.constr.
Require Import skylabs.ltac2.extra.internal.printf.

(** Minor extensions to [Ltac2.Control] *)
Module Control.
  Import Ltac2 Init Printf.
  Export Ltac2.Control.

  (** ** Backtracking control *)

  (** [nobacktrack f] runs [f] and panic if it backtracks. *)
  Ltac2 nobacktrack (f : unit -> 'a) : 'a :=
    Control.plus f Control.throw.

  Ltac2 once_nobacktrack (f : unit -> 'a) : 'a :=
    Control.once (fun () => nobacktrack f).

  (** ** Backtrace primitives *)
  Ltac2 Type 'a result_bt := [ Val_bt ('a) | Err_bt (exn, exninfo) ].
  Ltac2 @ external case_bt : (unit -> 'a) -> ('a * (exn -> 'a)) result_bt :=
    "ltac2_extensions" "case_bt".

  (** ** Running side-effecting computations *)

  (** [without_focus f] runs [f ()] once, independently of how many goals
      there are. This function is meant for running side-effecting code that
     is independent from the goal. *)
  Ltac2 without_focus (f : unit -> 'a) : 'a :=
    Control.focus 1 0 f.

  (** ** Proof state *)

  (** [new_goals_w_state evs] copies the current goal's state into the new
      goals. The function fails if there is not a single focused goal. *)
  Ltac2 @ external new_goals_w_state : evar list -> unit :=
    "ltac2_extensions" "new_goals_w_state".

  (** [focus_new_goal c cnt] extends the proof state with a new last goal of
      type [c], focuses on it, and invokes [cnt]. *)
  Ltac2 focus_new_goal (c : constr) (cnt : unit -> unit) :
      (evar * constr array) :=
    let (evar, inst) := Constr.Evar.of_constr (Constr.Evar.make c) in
    Control.enter (fun () =>
      Control.new_goal evar;
      Control.extend [] (fun () => ()) [cnt]
    );
    (evar, inst).

  (** [remove_future_goal] removes a goal from the list of future goals. This is
      necessary to work around https://github.com/coq/coq/issues/19138. *)
  Ltac2 @ external remove_future_goal : evar -> unit :=
    "ltac2_extensions" "remove_future_goal".

  (** ** Goal inspection *)

  Ltac2 Type hyp := ident * constr option * constr.

  Ltac2 pp_hyp : hyp pp := fun _ hyp =>
    let (id, mdef, ty) := hyp in
    match mdef with
    | None => fprintf "%a : %t" pp_ident id ty
    | Some def => fprintf "%a : %t := %t" pp_ident id ty def
    end.

  Ltac2 iter_hyps : (hyp -> unit) -> unit := fun f =>
    Control.enter (fun () => List.iter f (Control.hyps ())).

  (** [is_section_variable id] returns [true] if [id] is not a variable in the
      current environment. This seems to mean "being a section variable". *)
  Ltac2 @ external is_section_variable : ident -> bool :=
    "ltac2_extensions" "is_section_variable".

  Ltac2 Type exn ::= [ Multi_exn (exn list) ].

  (** This is a variant of [first0] ([first [ .. | .. ]]) which does not
      perform [Control.enter]. This is necessary to allow it to return a
      value: [Control.enter] forces a [unit] return type. *)
  Ltac2 first_of_impl (ls : (unit -> 'a) list) :=
   let rec go ls errs :=
        match ls with
        | t :: ls => orelse t (fun e => go ls (e :: errs))
        | []      =>
            let errs := List.rev errs in
            Control.zero (Multi_exn errs)
        end
      in
    Control.once (fun _ => go ls []).

  (** ** Goal evar *)

  Ltac2 @ external goal_evar : unit -> evar :=
    "ltac2_extensions" "goal_evar".

  (** ** Throws *)

  (** [throw_invalid fmt] throws [Invalid_argument] with a formatted message.
      It must be used via the [throw_invalid! fmt ...] notation. *)
  Ltac2 throw_invalid : ('a,'r) kprintf := fun fmt =>
    Message.Format.kfprintf (fun msg =>
      Control.throw (Invalid_argument (Some msg))) fmt.

  Ltac2 zero_invalid : ('a,'r) kprintf := fun fmt =>
    Message.Format.kfprintf (fun msg =>
      Control.zero (Invalid_argument (Some msg))) fmt.

  Ltac2 @ external user_err : message -> 'a :=
    "ltac2_extensions" "user_err".

  Ltac2 user_err_format : ('a,'r) kprintf := fun fmt =>
    Message.Format.kfprintf user_err fmt.

  Module Notations.
    Ltac2 Notation "throw_invalid!" fmt(format) := throw_invalid fmt.
    Ltac2 Notation "zero_invalid!"  fmt(format) := zero_invalid  fmt.
    Ltac2 Notation "user_err!"  fmt(format) := user_err_format fmt.

    Ltac2 Notation "first_of" "[" ls(list0(thunk(tactic(6)), "|")) "]" :=
      first_of_impl ls.
  End Notations.

  (** Access to the [ProofView] goal state capabilities. *)
  Module State.
    (** Extensible type of fields in the goal state, meant to be populated by
        variants __without__ arguments. The type parameter indicates what type
        can be stored in the corresponding field. Clients should define local
        aliases of the constructors they add to [t], since there is not way to
        make new constructors non-polymorphic. Accessing a field at different
        types leads to undefined behaviour. *)
    Ltac2 Type 'a t := [..].

    (** [get_state k] returns the value of type ['a] stored in field [k]. *)
    Ltac2 @ external get_state : 'a t -> 'a option :=
      "ltac2_extensions" "get_goal_state".

    (** [set_state k v] will set the state at field [k] to value [v]. *)
    Ltac2 @ external set_state : 'a t -> 'a -> unit :=
      "ltac2_extensions" "set_goal_state".
  End State.

  (** Variable renaming / shadowing. *)
  Module Shadow.
    Ltac2 Type exn ::= [ CannotRenameSectionVariable (ident) ].

    (** [rename1 old new] renames [old] to [new], shadowing any preexisting
        binding for [new]. It returns the list of renamings as a list of pairs
        of [(old_id, new_id)]. The list includes the original identifiers
        [(old, new)]. *)
    Ltac2 rename1 (old : Ident.t) (new : Ident.t) : ((ident * ident) list) :=
      if Ident.equal old new then [] else
      let ren := [(old, new)] in
      let ren :=
        let ids := List.map (fun (id, _, _) => id) (Control.hyps ()) in
        if List.exist (Ident.equal new) ids then
          let base :=
            (**
            TODO: Ideally, we would always pick a reserved identifier of
            the form [_new_] or [_newN_] but this code can pick
            [_new_N].

            Example: If [new] = [Hyp] and SSR has introduced [_Hyp_],
            this code can pick [_Hyp_0].
            <<
            Goal forall a b, a = b -> a + b = b + a.
            Proof.
              move=>a Hyp ?. shadow_rename a into Hyp.
            >>
            *)
            let s := String.concat "" ["_"; Ident.to_string new; "_"] in
            Option.get (Ident.of_string s)
          in
          let n := Fresh.fresh (Fresh.Free.of_ids ids) base in
          (new, n) :: ren
        else ren
      in
      List.iter (fun (old,_) =>
        if is_section_variable old then throw (CannotRenameSectionVariable old) else ()
      ) ren;
      Std.rename ren;
      ren.

    (** [rename old new] renames [old] to [new], shadowing any preexisting
        binding for [new]. *)
    Ltac2 rename old new := let _ := rename1 old new in ().

    (** [rename_many ren] renames all pairs [(old,new)] in the list [ren].
        It takes care to update [old] idents in [rens] whenever a renaming
        operation renamed [old] into something else. *)
    Ltac2 rename_many (rens : (ident * ident) list) : unit :=
      match rens with
      | [] => ()
      | [(old, new)] => rename old new
      | rens =>
          let rec go rens :=
            match rens with
            | [] => ()
            | (old, new) :: rens =>
              let ren := rename1 old new in
              let fixup ((old, new) as p) :=
                match List.find_opt (fun (old_id, _) => Ident.equal old old_id) ren with
                | Some (_, new_id) => (new_id, new)
                | None => p
                end
              in
              let rens := List.map fixup rens in
              go rens
            end
          in
          go rens
      end.
  End Shadow.
End Control.
Export Control.Notations.
