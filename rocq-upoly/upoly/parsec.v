(*
 * Copyright (C) 2023-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import stdpp.decidable.
Require Import skylabs.upoly.prelude.
Require Import skylabs.upoly.upoly.
Require Import skylabs.upoly.optionT.
Require Import skylabs.upoly.stateT.

(** ** Universes

    The parser definitions in this file use a mixture of universe-polymorphic
    datastructures and Coq's template-polymorphic standard library data
    structures. We generally use universe-polymorphic types for internal
    definitions and Coq standard library types for client-facing definitions.
    This is done to ease friction in clients which have to interoperate with
    other code that uses Coq's standard library.
 *)

Import UPoly.

(** [Next STREAM TKN] provides the [next] function to advance a stream of type
    [STREAM] and produce a single token of type [TKN] and an updated stream. If
    the stream reached its end, [next] returns [None]. *)
Class Next (STREAM TKN : Type) := {
  next_token : STREAM -> option (TKN * STREAM);
}.

(** [ParseString STREAM STR] provides the [parse_string] function which parses a
    string of type [STR] from a stream of type [STREAM] and returns the suffix
    of the stream. Here, "parsing" means that the string "matches" a prefix of
    the stream for some notion of "matching". In practice, most instances are
    going to correspond to some kind of prefix equality matching scheme. *)
Class ParseString (STREAM STR : Type) := {
  parse_string : STR -> STREAM -> option (STREAM)
}.

(** ** parsec
    Simple implementation of a parser combinator library.

    NOTE: [M] is a monad transformer so additional state can be
          threaded through the parsing.
 *)
Section parsec.
  Context `{N : Next STREAM TKN}.
  Context `{P : ParseString STREAM STR}.
  Context {F : Type -> Type} {MR : MRet F} {FM : FMap F} {MB : MBind F}.

  Definition M (T : Type) : Type :=
    stateT.M STREAM (optionT.M F) T.

  Definition run {T} (m : M T) : STREAM -> F _ :=
    fun str => optionT.run (stateT.run m str).

  #[global] Instance MRet_M : MRet M := @stateT.ret _ _ _.
  #[global] Instance FMap_M : FMap M := @stateT.map _ _ _.
  #[global] Instance MBind_M : MBind M := @stateT.bind _ _ _. (* prefer not to use this *)
  #[global] Instance Ap_M : Ap M := _.
  #[global] Instance MFail_M : MFail M := @stateT.fail _ _ _.
  #[global] Instance MLift_M : MLift F M := fun _ m => lift (optionT.lift m).
  #[global] Instance M_Alternative : Alternative M :=
    fun _ pl pr =>
      stateT.mk (fun s => alternative (stateT.runp pl s) (fun tt => stateT.runp (pr tt) s)).

  #[global] Hint Opaque M : typeclass_instances.
  #[local] Open Scope monad_scope.

  Definition any : M TKN :=
    let* l := stateT.get in
    match next_token l with
    | None => mfail
    | Some (b, bs) => const b <$> stateT.put bs
    end.

  (* end-of-stream *)
  Definition eos : M unit :=
    let* l := stateT.get in
    match next_token l with
    | None => mret tt
    | _ => mfail
    end.

  Definition run_full {T} (m : M T) : STREAM -> F (option T) :=
    fun str =>
      (fun x => match x with
             | Some (l, x) => match next_token l with None => Some x | Some _ => None end
             | _ => None
             end) <$> optionT.run (stateT.run ((fun x _ => x) <$> m <*> eos) str).

  Definition char (P : TKN -> bool) : M TKN :=
    let* c := any in
    if P c then mret c else mfail.

  Definition charP (P : TKN -> Prop) {_ : forall x, Decision (P x)} : M TKN :=
    char (fun x => bool_decide (P x)).

  Definition epsilon : M unit := mret tt.

  Definition or {T} (pl pr : M T) : M T :=
    pl <|> pr.

  Fixpoint anyOf {T} (ls : list (M T)) : M T :=
    match ls with
    | nil => mfail
    | l :: ls => l <|> anyOf ls
    end.

  (* NOTE: this is basically [sequence]/[transpose] *)
  Definition seqs {T} (ls : list (M T)) : M (list T) :=
    sequence ls.

  Definition optional {T} (p : M T) : M (option T) :=
    (Some <$> p) <|> mret None.

  Fixpoint star_ (fuel : nat) {T} (p : M T) : M (list T) :=
    let* x := optional p in
    match x with
    | None => mret nil
    | Some v =>
        match fuel with
        | 0 => mfail (* This is usually the programmers fault *)
        | S fuel => cons v <$> star_ fuel p
        end
    end.

  Definition star : forall {T}, _ := @star_ 1000.

  Definition plus {T} (p : M T) : M (list T) :=
    cons <$> p <*> star p.

  Definition peek : M (option TKN) :=
    let k l :=
      match next_token l with
      | None => None
      | Some (x, _) => Some x
      end
    in
    k <$> stateT.get.

  Definition sepBy {T} (sep : M unit) (p : M T) : M (list T) :=
    (cons <$> p <*> (star ((fun _ x => x) <$> sep <*> p))) <|> mret nil.

  #[local]
  Definition exact_ (b : STR) (input : STREAM)
      : optionT.M F (UTypes.prod STREAM unit) :=
    match parse_string b input with
    | Some input => mret (UTypes.pair input tt)
    | None => mfail
    end.

  Definition exact (b : STR) : M unit :=
    stateT.mk $ exact_ b.

   Definition not {T} (p : M T) : M unit :=
    stateT.mk $ fun bs => optionT.mk $
      let* v := parsec.run p bs in
      if v is None then mret (UTypes.Some $ UTypes.pair bs tt) else mret UTypes.None.
End parsec.

Arguments M _ _ _ : clear implicits.
