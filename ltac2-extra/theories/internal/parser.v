
Require Import skylabs.ltac2.extra.internal.init.
Require Import skylabs.ltac2.extra.internal.printf.
Require Import skylabs.ltac2.extra.internal.result.
Require Import skylabs.ltac2.extra.internal.string.

Module Parser.
  Import Ltac2 Constr Unsafe Printf Init.

  Module Ap := Result.Ap.

  Ltac2 Type 'a parser := constr -> 'a result.

  Ltac2 Type exn ::= [ Parser_choice_failure (exn, exn) ].

  Ltac2 parser_error (trm : constr) (s : string) :=
    Err (Invalid_argument (Some (fprintf "Expected %s, read (%a) %t" s pp_kind_tag (kind trm) trm))).

  Ltac2 parse_pair (parse_a : 'a parser) (parse_b : 'b parser) : ('a * 'b) parser :=
    fun trm =>
      lazy_match! trm with
      | (?x, ?y) => Ap.fmap (fun a b => (a, b))
                     (Ap.ap (parse_a x))
                     (Ap.ap (parse_b y))
                     Ap.done
      | _ => parser_error trm "(_, _)"
      end.

  Ltac2 parse_bool : bool parser :=
    fun trm =>
      lazy_match! trm with
      | true => Val true
      | false => Val false
      | _ => parser_error trm "bool literal"
      end.

  Ltac2 parse_pstring : string parser :=
    fun trm =>
      match kind trm with
      | String str => Val (Pstring.to_string str)
      | _ => parser_error trm "<string literal>"
      end.

  Ltac2 parse_stdlib_string : string parser :=
    fun trm =>
      match String.of_string_constr trm with
      | Some v => Val v
      | None => parser_error trm "String.string literal"
      end.

  Ltac2 parse_constr : constr parser :=
    fun trm => Val trm.

  Ltac2 run (parser : 'a parser) (c : constr) : 'a :=
    match parser c with
    | Val r => r
    | Err err => Control.throw err
    end.

End Parser.
