(*
 * Copyright (C) 2023-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.prelude.prelude.
Require Import Stdlib.Strings.PrimString.
Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Import bluerock.prelude.pstring.

Require Export bluerock.upoly.upoly.
Require Export bluerock.upoly.parsec.

#[local] Set Universe Polymorphism.
#[local] Unset Universe Minimization ToSet.

Import UPoly.
Section char_parsec.
  Context {F : Type -> Type} {MR : MRet F} {FM : FMap F} {MB : MBind F}.
  Notation STREAM := (Uint63.int * PrimString.string)%type.
  Notation M := (M STREAM F).
  Notation TKN := PrimString.char63.

  #[global] Instance bs_next : Next STREAM TKN := {|
    next_token '(i, str) :=
      if (i <? PrimString.length str)%uint63 then
        Some (PrimString.get str i, ((i + 1)%uint63, str))
      else None
  |}.

  #[global] Instance bs_parse_string : ParseString STREAM PrimString.string := {|
    parse_string s '(i, str) :=
      let slen := PrimString.length s in
      if (slen <=? PrimString.length str - i)%uint63 then
        match PrimString.compare s (PrimString.sub str i slen) with
        | Eq => Some (i + slen, str)%uint63
        | _ => None
        end
      else
        None
  |}.

  Definition run_bs {T} (p : M T) (b : STREAM) : F (option (STREAM * T)) := run p b.

  Definition run_full_bs {T} (p : M T) (b : STREAM) : F (option T) := run_full p b.

  Definition digit : M PrimString.char63 :=
    char (fun x => (("0".(char63_wrap) ≤? x) && (x ≤? "9".(char63_wrap)))%char63%uint63).

  Definition exact_bs (b : PrimString.string) : M unit :=
    exact $ b.

  Definition exact_char (b : PrimString.char63) : M unit :=
    fmap (fun _ => ()) $ char (fun b' => bool_decide (b = b')).

  Import Stdlib.Strings.Ascii.
  Definition quoted {U V T} (pre : M U) (post : M V) (p : M T) : M T :=
    (fun _ x _ => x) <$> pre <*> p <*> post.

  Definition ws : M unit :=
    const () <$> (star $ char (fun x => is_space x)).

  Definition ignore_ws {T} (p : M T) : M T :=
    quoted ws ws p.

  (* A note about effects:
     [not p] will roll-back monadic changes of parsec, but will *not* roll back
     monadic changes in [F]. Therefore, users should be careful about [F] effects
     in [p]. Generally, [p] should be effect free in [F].
   *)
End char_parsec.


(* The combination of [compile] and [interp] create an optimized parser
   based on a list of literals.

   More optimizations are likely possible here.
 *)
Module keyword_set.
Section keyword_set.
  Import parsec.
  Import UPoly.

  #[local] Open Scope monad_scope.

  Context {token : Set}.
  Context {token_dec : EqDecision token}.
  #[local] Fixpoint deriv {A} (ls : list (list token * A)) (b : token)
    : option (option A * list (list token * A) * list (list token * A)) :=
    match ls with
    | nil => Some (None, nil, nil)
    | ([], t) :: rest =>
        let* '(a,l,r) := deriv rest b in
        match a with
        | None => Some (Some t, l, r)
        | _ => None
        end
    | (x :: xs, t) :: rest =>
        let* '(a, l, r) := deriv rest b in
        if bool_decide (x = b) then
          Some (a, (xs, t) :: l, r)
        else
          Some (a, l, (x :: xs, t) :: r)
    end.

  (* Generic compilation infrastructure *)
  Inductive DTree {T : Type} : Type :=
  | FAIL
  | OK (_ : list token) (_ : T)
  | OR (_ _ : DTree)
  | COMMIT (_ : token) (_ : DTree) (_ : DTree).
  Arguments DTree _ : clear implicits.

  #[local] Definition opt_COMMIT {T} a (b c : DTree T) :=
    match b , c with
    | OK xs v , FAIL => OK (a :: xs) v
    | _ , _ => COMMIT a b c
    end.

  Fixpoint compile {A} (fuel : nat) (ls : list (list token * A)) {struct fuel} : option (DTree A) :=
    match ls with
    | nil => Some FAIL
    | (xs, t) :: nil =>
        Some (OK xs t)
    | ([], t) :: ls =>
        match fuel with
        | S fuel =>
            let* r := compile fuel ls in
            mret (OR r (OK [] t))
        | _ => None
        end
    | (b :: bs, t) :: ls =>
        let* '(eps, here, rest) := deriv ls b in
        match fuel with
        | S fuel =>
            let* rest := opt_COMMIT b <$> (compile fuel $ (bs, t) :: here) <*> (compile fuel rest) in
            match eps with
            | None => mret rest
            | Some v => mret $ OR rest (OK [] v)
            end
        | _ => None (* compilation failure *)
        end
    end.

  Context {Mbase : Type -> Type}.
  Context {RET : MRet Mbase} {FMAP : FMap Mbase}
    {AP : Ap Mbase} {MBIND : MBind Mbase}.
  Notation STREAM := (Uint63.int * PrimString.string)%type.
  Notation M := (M@{Set _ _ _ _ _ _ _ _} STREAM Mbase).

  #[local] Fixpoint seqs_to {T} (tokenD : token -> M ()) (v : T) (m : list token) : M T :=
    match m with
    | nil => mret v
    | m :: ms => tokenD m *> seqs_to tokenD v ms
    end.

  Fixpoint interp {T} (tokenD : token -> M ()) (dt : DTree T) : M T :=
    match dt with
    | FAIL => mfail
    | OK ts v => seqs_to tokenD v ts
    | OR a b => interp tokenD a <|> interp tokenD b
    | COMMIT b thn els =>
        let* x := optional (tokenD b) in
        match x with
        | None => interp tokenD els
        | Some dt => interp tokenD thn
        end
    end.
End keyword_set.
End keyword_set.
