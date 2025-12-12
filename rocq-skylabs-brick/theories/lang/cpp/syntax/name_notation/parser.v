(*
 * Copyright (C) 2023-2025 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import stdpp.prelude.
Require Import bluerock.prelude.base.
Require Import bluerock.upoly.upoly.
Require Import bluerock.upoly.option.
Require Import bluerock.upoly.list.
Require Import bluerock.prelude.parsec.
Require Import bluerock.lang.cpp.syntax.core.
Require Import bluerock.lang.cpp.syntax.types.
Require Import Stdlib.Strings.PrimString.
Require Import bluerock.prelude.pstring.
Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Import bluerock.lang.cpp.syntax.translation_unit.

(** ** A parser for C++ names.

    This does not currently support all of C++ names, e.g. those
    that contain expressions. In general, it may be difficult to support
    some expressions.
 *)

Import Uint63Notations.
Definition ident_char (b : PrimString.char63) : bool :=
     in_range_incl "a" "z" b
  || in_range_incl "A" "Z" b
  || (b =? "_".(char63_wrap))%char63%uint63.

Definition digit_char (b : char63) : bool :=
  (("0".(char63_wrap) ≤? b) && (b ≤? "9".(char63_wrap)))%char63%uint63.

Module internal.
  Import parsec.
  Import UPoly.

  #[local] Open Scope monad_scope.

  Section with_M.
    Context {Mbase : Type -> Type}.
    Context {RET : MRet Mbase} {FMAP : FMap Mbase} {AP : Ap Mbase} {MBIND : MBind Mbase}.

    Notation M := (parsec.M@{Set _ _ _ _ _ _ _ _} (Uint63.int * PrimString.string) Mbase).

    Fixpoint get_ident (s : PrimString.string) (start len : int) (f : char63 -> bool) (fuel : nat)
      : int * PrimString.string :=
      let idx := (start + len)%uint63 in
      match fuel with
      | 0 => (start + len, PrimString.sub s start len)
      | S fuel =>
          if ltb idx (PrimString.length s) then
            let c := PrimString.get s idx in
            if f c then
              get_ident s start (len + 1)%uint63 f fuel
            else
              (start + len, PrimString.sub s start len)
          else
            (start + len, PrimString.sub s start len)
      end%uint63.

    Definition ident : M PrimString.string :=
      let* i :=
        (
          stateT.mk $ fun '(idx, str) =>
              if ltb idx (PrimString.length str) then
                if ident_char (PrimString.get str idx) then
                  let '(fin, s) := get_ident str idx 1%uint63 (fun x => ident_char x || digit_char x) 1000 in
                  optionT.mk (mret (UTypes.Some (UTypes.pair (fin, str) s)))
                else optionT.mk (mret (UTypes.None))
              else
                optionT.mk (mret (UTypes.None)))
      in
      if bool_decide (i ∈ ["const";"volatile";"char";"signed";"unsigned";"float";"double";"int";"long";"short";
                           "typename";"class";"struct";"union";
                           "for";"while";"do";"try";"catch"]%pstring)
      then mfail else mret i
    .

    Notation exact bs := (exact_bs bs).

    (* a maximal identifier *)
    Definition keyword_no_ws (s : PrimString.string) : M unit :=
      let* _ := exact s in
      let* _ := not $ char (fun a => ident_char a || digit_char a) in
      mret ().

    Definition keyword (b : PrimString.string) : M unit :=
      ws *> keyword_no_ws b <* ws.

    Definition punct_char (c : char63) : Prop :=
      in_range_incl_excl "!" "0" c \/
      in_range_excl      "9" "A" c \/
      in_range_excl      "Z" "a" c \/
      in_range_excl      "z" 127%uint63 c.

    Definition space_char (c : char63) : Prop :=
      c ∈ [9; 10; 11; 12; 13; 32]%uint63.

    (* TODO: ideally, i would like to say that this does not contain additional characters. *)
    Definition op_token (s : PrimString.string) : M unit :=
      let* _ := ws in
      let* _ := exact s in
      ws.

    Definition decimal : M N :=
      let make ls := fold_left (fun acc x => 10 * acc + x)%N ls 0%N in
      make <$> plus ((fun x => Z.to_N $ to_Z $ x - "0".(char63_wrap))%char63%uint63 <$> digit).

    Definition parse_qualifiers : M function_qualifiers.t :=
      let quals :=
        star (anyOf $ [const function_qualifiers.Nc <$> keyword "const";
                       const function_qualifiers.Nv <$> keyword "volatile";
                       const function_qualifiers.Nr <$> op_token "&&";
                       const function_qualifiers.Nl <$> op_token "&"]) in
      fold_right function_qualifiers.join function_qualifiers.N <$> quals.

    Definition basic_types : list (list PrimString.string * type) :=
      let s_or_u_l (b : list PrimString.string) (s u : type) :=
        [(b, s); ("signed" :: b, s); ("unsigned" :: b, u)]%pstring
      in
      let s_or_u b := s_or_u_l [b] in
      [ (["bool"], Tbool)
      ; (["void"], Tvoid)
      ; (["wchar_t"], Twchar_t)
      ; (["char8_t"], Tchar8_t)
      ; (["char16_t"], Tchar16_t)
      ; (["char32_t"], Tchar32_t)
      ; (["char"], Tchar)
      ; (["unsigned"; "char"], Tuchar)
      ; (["signed"; "char"], Tschar)
      ; (["uint128_t"], Tuint128_t)
      ; (["int128_t"], Tint128_t) ]%pstring ++
      s_or_u "int128"%pstring Tint128_t Tuint128_t ++
      s_or_u "__int128"%pstring Tint128_t Tuint128_t ++
      s_or_u_l ["short";"int"]%pstring Tshort Tushort ++
      s_or_u "short"%pstring Tshort Tushort ++
      s_or_u "int"%pstring Tint Tuint ++
      s_or_u_l ["long";"long";"int"]%pstring Tlonglong Tulonglong ++
      s_or_u_l ["long";"long"]%pstring Tlonglong Tulonglong ++
      s_or_u_l ["long";"int"]%pstring Tlong Tulong ++
      s_or_u "long"%pstring Tlong Tulong ++
      [ (["unsigned"], Tuint)
      ; (["signed"], Tint)
      ; (["nullptr_t"], Tnullptr)
      ; (["float16"], Tfloat16)
      ; (["float128"], Tfloat128)
      ; (["float"], Tfloat)
      ; (["double"], Tdouble)
      ; (["long"; "double"], Tlongdouble) ]%pstring.

    Fixpoint interleave {A} (p : A) (ls : list A) : list A :=
      match ls with
      | nil => p :: nil
      | l :: ls => p :: l :: interleave p ls
      end.

    #[local] Definition basic_type_otree :=
      Eval vm_compute in keyword_set.compile 1000 $ (fun '(x,y) => (interleave None (List.map Some x), y)) <$> @basic_types.

    Definition basic_type : M type :=
      Eval red in
      match basic_type_otree as X return X = basic_type_otree -> _ with
      | None => fun pf => ltac:(exfalso; inversion pf)
      | Some o => fun _ =>
        let token x := match x with
                       | None => ws
                       | Some b => keyword_no_ws b
                       end in
        keyword_set.interp token o
      end eq_refl.

    Definition operators : list (PrimString.string * OverloadableOperator) :=
      (* this is used in an early commit manner, so longer operators
         need to come first
         TODO: list is incomplete
       *)
      [ ("~", OOTilde)
      ; ("<=>", OOSpaceship)
      ; ("!=", OOExclaimEqual)
      ; ("!", OOExclaim)
      ; ("++", OOPlusPlus)
      ; ("--", OOMinusMinus)
      ; ("&&", OOAmpAmp)
      ; ("||", OOPipePipe)
      ; ("==", OOEqualEqual)
      ; ("=", OOEqual)
      ; ("<<=", OOLessLessEqual)
      ; (">>=", OOGreaterGreaterEqual)
      ; ("<=", OOLessEqual)
      ; ("<<", OOLessLess)
      ; (">=", OOGreaterEqual)
      ; (">>", OOGreaterGreater)
      ; ("+=", OOPlusEqual)
      ; ("-=", OOMinusEqual)
      ; ("%=", OOPercentEqual)
      ; ("/=", OOSlashEqual)
      ; ("*=", OOStarEqual)
      ; ("&=", OOAmpEqual)
      ; ("|=", OOPipeEqual)
      ; ("^=", OOCaretEqual)
      ; ("->*", OOArrowStar)
      ; ("->", OOArrow)
      ; ("<", OOLess)
      ; (">", OOGreater)
      ; ("[]", OOSubscript)
      ; ("()", OOCall)
      ; ("new[]", OONew true)
      ; ("delete[]", OODelete true)
      ; ("new", OONew false)
      ; ("delete", OODelete false)
      ; ("co_await", OOCoawait)
      ; (",", OOComma)
      ; ("*", OOStar)
      ; ("+", OOPlus)
      ; ("-", OOMinus)
      ; ("/", OOSlash)
      ; ("%", OOPercent)
      ; ("&", OOAmp)
      ; ("^", OOCaret)
      ; ("|", OOPipe)
      ]%pstring.

    Definition operator : M OverloadableOperator :=
      let* _ := ws in
      let* res := (anyOf $ (fun '(lex, syn) => const syn <$> exact lex) <$> operators) in
      let* _ := ws in
      mret res.

    Definition spaced (s : PrimString.string) : M unit :=
      let* _ := ws in
      let* _ := exact s in
      ws.

    Definition get_args (ls : list type) : list type :=
      match ls with
      | [Tvoid] => []
      | _ => ls
      end.

    Definition NEXT {T} (n : nat) (f : nat -> M T) : M T :=
      match n with
      | 0 => mfail
      | S n => f n
      end.

  End with_M.

  Notation STREAM := (Uint63.int * PrimString.string)%type.
  Notation TKN := PrimString.char63.

  #[local] Definition M := (parsec.M STREAM (eta option)).

  #[local] Instance M_ret : MRet M := _.
  #[local] Instance M_map : FMap M := _.
  #[local] Instance M_ap : Ap M := _.
  #[local] Instance M_bind : MBind M := _.
  #[local] Instance M_alt : Alternative M := _.

  Definition run {T} (m : M T) (str : PrimString.string) : option (STREAM * T) :=
    match parsec.run_bs m (0%uint63, str) with
    | Some (Datatypes.Some (rest, result)) => Some (rest, result)
    | _ => None
    end.

  Definition run_full {T} (p : M T) (str : PrimString.string) : option T :=
    let m : M T := (fun x _ => x) <$> p <*> eos in
    fmap (M:=eta option) (fun '(_,b) => b) $ run m str.

  Notation exact bs := (exact_bs bs).

  Definition parens {T} (m : M T) : M T := quoted (spaced "(") (spaced ")") m.

  Definition commit {T U} (test : M T) (yes : T -> M U) (no : M U) : M U :=
    let* yn := optional test in
    match yn with
    | Some y => yes y
    | None => no
    end.

  Section with_lang.
    Variant Result : Set :=
    | NoCheck
    | Unknown
    | Alias (_ : type)
    | IsEnum
    | IsStruct.
    Variable resolve_name : name -> Result.

    (** classification of names based to account for destructors and overloadable
        operators. *)
    Variant name_type : Set :=
      | Simple (_ : PrimString.string)
      | Dtor (_ : PrimString.string)
      | FirstDecl (_ : PrimString.string)
      | FirstChild (_ : PrimString.string)
      | Anon (_ : N)
      | Op (_ : OverloadableOperator)
      | OpConv (_ : type)
      | OpLit (_ : PrimString.string).

    Section body.
      Notation name_component := (name_type * option (list type * function_arity * function_qualifiers.t) * option (list temp_arg))%type.
      Variable parse_type : unit -> M type.
      Variable parse_name : unit -> M name.
      Variable parse_name_component : unit -> M name_component.
      Variable parse_expr : unit -> M Expr.

      Definition parse_args (no_start_paren : bool) : M (list type * function_arity) :=
        let args := sepBy (spaced ",") (parse_type ()) in
        let arity :=
          let arity a :=
            match a with
            | None => Ar_Definite
            | Some _ => Ar_Variadic
            end
          in
          arity <$> optional ((fun _ _ => ()) <$> spaced "," <*> spaced "...")
        in
        if no_start_paren then
          (pair <$> (get_args <$> args) <*> arity) <* spaced ")"
        else
          parens (pair <$> (get_args <$> args) <*> arity).

      Definition parse_postfix_type : M (type -> type) :=
        let entry := fix entry fuel :=
          let array_entry :=
            (exact "]" *> mret Tincomplete_array) <|>
              (let* n := decimal in
               let* _ := exact "]" in
               mret (fun x => Tarray x n))  <|>
              (let* n := parse_expr () in
               let* _ := exact "]" in
               mret (fun x => Tvariable_array x n))
          in
          let function_entry :=
            let qualified :=
              let* (post : list (type -> type)) :=
                (star (NEXT fuel entry) : M (list (type -> type))) <* ws <* exact ")" in
              if post is nil then
                mret (fun rt => Tfunction (FunctionType rt []))
              else
                let post := fold_left (fun t f => f t) post in
                let* '(args, ar) := parse_args false in
                mret (fun rt => post $ Tfunction (FunctionType (ft_arity:=ar) rt args))
            in
            qualified <|>
            (let* '(args, ar) := parse_args true in
             mret (fun rt => Tfunction (FunctionType (ft_arity:=ar) rt args)))
          in
          let* _ := ws in
          (let* _ := exact "&&" in mret Trv_ref) <|>
            (let* _ := exact "&" in mret Tref) <|>
            (let* _ := exact "*" in mret Tptr) <|>
            (let* _ := keyword "const" in mret $ fun x => tqualified QC x) <|>
            (let* _ := keyword "volatile" in mret $ fun x => tqualified QV x) <|>
            (exact "[" *> array_entry) <|>
            (exact "(" *> function_entry) <|>
            (let* _ := exact "(" in
             let* nm := parse_name () in
             let* _ := spaced "::" in
             let* _ := exact "*" in
             let* _ := spaced ")" in
             let* '(args, ar) := parse_args false in
             mret (fun rt => Tmember_pointer (Tnamed nm) $ Tfunction (FunctionType (ft_arity:=ar) rt args)))
        in
        fold_left (fun t f => f t) <$> star (entry 100).

      Definition name_for_parse (def : name -> type) (opt : option ()) (nm : name) : M type :=
        match resolve_name nm return M type with
        | NoCheck => mret $ def nm
        | Alias ty => mret ty
        | IsEnum => match def nm return M type with
                    | Tenum _ as def => mret def
                    | Tnamed _ =>
                        match opt with
                        | None => mret $ Tenum nm
                        | _ => mfail
                        end
                    | _ => mfail
                    end
        | IsStruct => match def nm with
                      | Tnamed _ as def => mret def
                      | Tenum _ => match opt with
                                   | None => mret $ Tnamed nm
                                   | _ => mfail
                                   end
                      | _ => mfail
                      end
        | Unknown => mfail
        end.

    (* The core parsers are based on fuel to handle the mutual recursion *)
    Definition parse_type' : M type :=
      let* quals :=
        star (((fun _ => tqualified QC) <$> keyword "const") <|>
              ((fun _ => tqualified QV) <$> keyword "volatile"))
      in
      let build_named_type ctor nm :=
        match nm with
        | Nglobal (Nfunction function_qualifiers.N nm args) =>
            (fun x => Tfunction $ FunctionType x args) <$> (ctor $ Nglobal $ Nid nm)
        | Nscoped scp (Nfunction function_qualifiers.N nm args) =>
            (fun x => Tfunction $ FunctionType x args) <$> (ctor $ Nscoped scp (Nid nm))
        | Ndependent t => mret $ t
        | _ => ctor nm
        end
      in
      let* t :=
        basic_type <|>
        (commit (exact "(") (fun _ => parse_type () <* exact ")")
         $ commit (exact "$") (fun _ => let* var := ident in
                                     let* nested := star (exact "::" *> (Nid <$> ident)) in
                                     mret match nested with
                                     | nil => Tparam var
                                     | _ => Tnamed (fold_right (fun an n => Nscoped n an) (Ndependent (Tparam var)) nested)
                                     end)
         $ commit (exact "#" <|> keyword "enum")
                (fun e => let* n := parse_name () in
                     build_named_type (name_for_parse Tenum (Some e)) n)
         $ let* kw := optional (keyword "struct" <|> keyword "class") in
           let* n := parse_name () in
           build_named_type (name_for_parse Tnamed kw) n)
      in
      let* post := parse_postfix_type in
      mret $ post (List.fold_right (fun f x => f x) t quals).

    Fixpoint as_conv (q : function_qualifiers.t) (t : type) : option (type * list type * function_qualifiers.t) :=
      match t with
      | Tqualified cv t =>
          as_conv (function_qualifiers.join q $ function_qualifiers.mk (q_const cv) (q_volatile cv) Prvalue) t
      | Tref t => as_conv (function_qualifiers.join q $ function_qualifiers.mk false false Lvalue) t
      | Trv_ref t => as_conv (function_qualifiers.join q $ function_qualifiers.mk false false Xvalue) t
      | Tfunction ft => Some (ft.(ft_return), ft.(ft_params), q)
      | _ => None
      end.

    Definition mk_atomic_name (last : option PrimString.string) (nm : name_type)
      (args : option (list type * function_arity * _)) : M atomic_name :=
     match args with
     | None => match nm with
              | Simple nm => mret $ Nid nm
              | FirstDecl nm => mret $ Nfirst_decl nm
              | FirstChild nm => mret $ Nfirst_child nm
              | Anon n => mret $ Nanon n
              | OpConv t =>
                  (* NOTE: this is a hack because <<int()>> is parsed as a function type. *)
                  match as_conv function_qualifiers.N t with
                  | Some (ret, args, q) =>
                      match args with
                      | nil => mret $ Nop_conv q ret
                      | _ => mfail
                      end
                  | None => mfail
                  end
              | Dtor _
              | Op _
              | OpLit _ => mfail
              end
     | Some (args, ar, quals) =>
         match nm with
         | Dtor nm =>
             if bool_decide (Some nm = last /\ args = []) then
               mret $ Ndtor
             else mfail
         | Simple nm => mret $ Nfunction quals nm args
         | Op oo => mret $ Nop quals oo args
         | OpConv t =>
             match args with
             | nil => mret $ Nop_conv quals t
             | _ => mfail
             end
         | OpLit n =>
             match quals with
             | function_qualifiers.N => mret $ Nop_lit n args
             | _ => mfail
             end
         | FirstDecl n => mfail
         | FirstChild n => mfail
         | Anon _ => mfail
         end
     end.

    Section mfold_left.
      Context {T U : Type}.
      Variable f : T -> U -> M T.
      Fixpoint mfold_left (ls : list U) (acc : T) : M T :=
        match ls with
        | nil => mret acc
        | l :: ls =>
            let* acc := f acc l in mfold_left ls acc
        end.
    End mfold_left.

    Definition parse_name': M name :=
     commit (keyword "typename") (fun _ => Ndependent <$> parse_type ()) $
     (let* (x : list (name_type * _ * _)) :=
        optional (op_token "::") *> sepBy (op_token "::") (parse_name_component ())
      in
      match x with
      | nil => mfail (* unreachable *)
      | (nt, args, oinst) :: xs =>
          let* nm := mk_atomic_name None nt args in
          let sp oi :=
            match oi with
            | None => fun x => x
            | Some i => fun x => Ninst x i
            end
          in
          let* root :=
            (mret $ sp oinst $ Nglobal nm)
          in
          let f '(acc, last) '(nt, args, oinst) :=
            let last_name :=
              match last with
              | Nid x => Some x
              | _ => None
              end
            in
            let* nm := mk_atomic_name last_name nt args in
            mret match nm with
              | Nfunction function_qualifiers.N fnm args =>
                  if bool_decide (Nid fnm = last) then
                    (sp oinst (Nscoped acc $ Nctor args), nm)
                  else
                    (sp oinst (Nscoped acc nm), nm)
              | _ =>
                  (sp oinst (Nscoped acc nm), nm)
              end
          in
          fst <$> mfold_left f xs (root, nm)
      end).

   Fixpoint template_arg (fuel : nat) : M temp_arg :=
     commit (keyword "template") (fun _ => Atemplate <$> parse_name')
     $
     (Atype <$> parse_type ()) <|> (Avalue <$> parse_expr ()) <|>
     (Apack <$> (spaced "...<" *>
      match fuel with
      | S fuel =>
          sepBy (op_token ",") (template_arg fuel)
      | _ => mfail
      end
      <* spaced ">")).

   (* name components basically amount to atomic names with an optional template
       specialization after them. They are complex because function names include their
       arguments.
     *)
    Definition parse_name_component' : M (_ * _ * option (list temp_arg)) :=
      let* (nm : name_type) :=
        let operator _ :=
          (Op <$> operator) <|>
          (commit (exact """""_") (fun _ => OpLit <$> ident)
             $ OpConv <$> parse_type ())
        in
        commit (keyword "operator") operator
        $ commit (op_token "~") (fun _ => Dtor <$> ident)
        $ commit (exact "@") (fun _ => (Anon <$> decimal) <|> (FirstDecl <$> ident))
        $ commit (exact ".") (fun _ => FirstChild <$> ident) (Simple <$> ident)
      in
      let* template_args :=
        let template_arg := template_arg 10 in
        optional (quoted (spaced "<") (spaced ">") $ sepBy (op_token ",") template_arg) in
      let parse_args : M _ :=
        optional (let* '(args, arity) := parse_args false in
                  let* quals := parse_qualifiers in
                  mret (args, arity, quals))
      in
      let* a := parse_args in
      mret (nm, a, template_args)
    .

    Definition parse_z : M Z :=
      let num sgn n :=
        match sgn with
        | None => Z.of_N n
        | Some _ => Z.opp $ Z.of_N n
        end
      in
      num <$> optional (op_token "-") <*> decimal.

    Definition escape_table : list (TKN * TKN) := Eval vm_compute in
      (fun x => (char63_wrap x.1, char63_wrap x.2)) <$>
        [("\", "\")%char63;
         ("n", wrap_char63 13%uint63);
         ("t", wrap_char63 9%uint63);
         ("r", wrap_char63 10%uint63)]%char63.

    Definition cpp_char : M N :=
      let get : M TKN :=
        let* c := char (fun _ => true) in
        if bool_decide (c = "\".(char63_wrap))%char63 then
          let* c := char (fun _ => true) in
          match list_find (fun k_v => k_v.1 = c) escape_table with
          | None => mfail
          | Some k_v => mret k_v.2.2
          end
        else
          mret c
      in (fun x => Z.to_N $ to_Z x) <$> get.


    Definition parse_expr' : M Expr :=
      let* _ := ws in
      let int_literal :=
        let* num := parse_z in
        let* suffix := optional (anyOf [(const Tlonglong <$> keyword "ll");
                                        (const Tlong <$> keyword "l");
                                        (const Tulonglong <$> keyword "ull");
                                        (const Tulong <$> keyword "ul");
                                        (const Tuint <$> keyword "u");
                                        (const Tbool <$> keyword "b")]) in
        let ty :=
          match suffix with
          | None => Tint
          | Some ty => ty
          end
        in
        mret $ Eint num ty
      in
      let char_literal :=
        let* ty := optional (anyOf [(const Tchar8 <$> keyword "u8");
                                     (const Tchar16 <$> keyword "u");
                                     (const Tchar32 <$> keyword "U");
                                     (const Twchar <$> keyword "L")]) in
        let ty : type :=
          match ty with
          | None => Tchar
          | Some t => t
          end
        in
        (fun n => Echar n ty) <$> exact "'" *> cpp_char <* exact "'"
      in
      let simple_literal :=
        anyOf [(const (Ebool true) <$> keyword "true");
                 (const (Ebool false) <$> keyword "false");
                 (const Enull <$> keyword "nullptr")]
      in
      let param := (fun _ => Eparam) <$> exact "`" <*> ident in
      let global :=
        (* NOTE: there is no way to get the type of the global here.
           To make this work, we need to remove this information from
           the expression. *)
        Eglobal <$> parse_name () <*> mfail
      in
      int_literal <|> char_literal <|> simple_literal <|> param <|> global.
    End body.

    Fixpoint parse_type (fuel : nat) :=
      parse_type' (fun _ => NEXT fuel parse_type) (fun _ => NEXT fuel parse_name) (fun _ => NEXT fuel parse_expr)
    with parse_name (fuel : nat) :=
      parse_name' (fun _ => NEXT fuel parse_type) (fun _ => NEXT fuel parse_name_component)
    with parse_name_component (fuel : nat) :=
      parse_name_component' (fun _ => NEXT fuel parse_type) (fun _ => NEXT fuel parse_name_component) (fun _ => NEXT fuel parse_expr)
    with parse_expr (fuel : nat) :=
      parse_expr' (fun _ => NEXT fuel parse_name).

  End with_lang.

  #[global] Arguments Result : clear implicits.

  Definition check (tu : translation_unit) (n : name) :=
    match tu.(types) !! n with
    | None => Unknown
    | Some gd =>
        match gd with
        | Gunion _ | Gstruct _ => IsStruct
        | Genum _ _ => IsEnum
        | Gtypedef t => Alias t
        | _ => NoCheck
        end
    end.
  Definition no_check : name -> Result :=
    fun _ => NoCheck.

End internal.

Definition parse_name_with (tu : translation_unit) (input : PrimString.string) : option name :=
  internal.run_full (internal.parse_name (internal.check tu) 1000) input.

Definition parse_type_with (tu : translation_unit) (input : PrimString.string) : option type :=
  internal.run_full (internal.parse_type (internal.check tu) 1000) input.

Definition parse_name (input : PrimString.string) : option name :=
  internal.run_full (internal.parse_name internal.no_check 1000) input.

Definition parse_type (input : PrimString.string) : option type :=
  internal.run_full (internal.parse_type internal.no_check 1000) input.

Module Type TESTS.
  #[local] Definition TEST (input : PrimString.string) (nm : name) : Prop :=
    (parse_name input) = Some nm.
  #[local] Definition TEST_fail (input : PrimString.string) : Prop :=
    (parse_name input) = None.
  #[local] Definition TEST_type (input : PrimString.string) (nm : type) : Prop :=
    (parse_type input) = Some nm.

  #[local] Definition Msg : name := Nglobal $ Nid "Msg".

  Succeed Example _0 : TEST "Msg" Msg := eq_refl.
  Succeed Example _0 : TEST "::Msg" Msg := eq_refl.
  Succeed Example _0 : TEST "Msg::@0" (Nscoped Msg (Nanon 0)) := eq_refl.
  Succeed Example _0 : TEST "Msg::Msg()" (Nscoped Msg (Nctor [])) := eq_refl.
  Succeed Example _0 : TEST "Msg::~Msg()" (Nscoped Msg (Ndtor)) := eq_refl.
  Succeed Example _0 :
    let targs := Avalue <$> [Eint 1 Tulong;
                             Eint (-2) Tlong;
                             Eint 3 Tulonglong;
                             Eint (-4) Tlonglong;
                             Eint 5 Tuint;
                             Eint 6 Tint] in
    TEST "Msg<1ul, -2l, 3ull, -4ll, 5u, 6>::Msg()" (Nscoped (Ninst Msg targs) (Nctor [])) := eq_refl.
  Succeed Example _0 :
    let targs := Atype <$> [Tulong;
                            Tlong;
                            Tulonglong;
                            Tlonglong;
                            Tuint; Tint] in
    TEST "Msg<unsigned long, long, unsigned long long, long long, unsigned int, int>::Msg()" (Nscoped (Ninst Msg targs) (Nctor [])) := eq_refl.
  Succeed Example _0 : TEST "Msg::Msg(int)" (Nscoped Msg (Nctor [Tint])) := eq_refl.
  Succeed Example _0 : TEST "Msg::Msg(long)" (Nscoped Msg (Nctor [Tlong])) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator=(const Msg&)" (Nscoped Msg (Nop function_qualifiers.N OOEqual [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator=(const Msg&&)" (Nscoped Msg (Nop function_qualifiers.N OOEqual [Trv_ref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator new()" (Nscoped Msg (Nop function_qualifiers.N (OONew false) [])) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator new[]()" (Nscoped Msg (Nop function_qualifiers.N (OONew true) [])) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator   delete()" (Nscoped Msg (Nop function_qualifiers.N (OODelete false) [])) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator delete[]()" (Nscoped Msg (Nop function_qualifiers.N (OODelete true) [])) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator int()" (Nscoped Msg (Nop_conv function_qualifiers.N Tint)) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator int() const" (Nscoped Msg (Nop_conv function_qualifiers.Nc Tint)) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator int() const volatile" (Nscoped Msg (Nop_conv function_qualifiers.Ncv Tint)) := eq_refl.
  Succeed Example _0 : TEST "Msg::operator int() &" (Nscoped Msg (Nop_conv function_qualifiers.Nl Tint)) := eq_refl.

  Succeed Example _0 : TEST "foo_client(int[2]&, int const*, bool*, int**, char*)" (Nglobal (Nfunction function_qualifiers.N "foo_client" [Tref (Tarray Tint 2); Tptr (Tconst Tint); Tptr Tbool; Tptr (Tptr Tint); Tptr Tchar])) := eq_refl.
  Succeed Example _0 : TEST "DlistInternal::iterator::operator!=(const DlistInternal::iterator&) const"
                 (Nscoped (Nscoped (Nglobal (Nid "DlistInternal")) (Nid "iterator"))
                    (Nop function_qualifiers.Nc OOExclaimEqual [Tref (Tqualified QC (Tnamed (Nscoped (Nglobal (Nid "DlistInternal")) (Nid "iterator"))))])) := eq_refl.
  Succeed Example _0 : TEST "intrusive::List_internal::iterator::iterator(intrusive::List_internal::Node*)"
                 (Nscoped (Nscoped (Nscoped (Nglobal (Nid "intrusive")) (Nid "List_internal")) (Nid "iterator"))
                    (Nctor [Tptr (Tnamed (Nscoped (Nscoped (Nglobal (Nid "intrusive")) (Nid "List_internal")) (Nid "Node")))])) := eq_refl.
  Succeed Example _0 : TEST "span<const int, 1ul>::span(const int*, unsigned long)"
                         (Nscoped (Ninst (Nglobal (Nid "span")) [Atype (Tqualified QC Tint);
                                                                 Avalue (Eint 1 Tulong)])
                            (Nctor [Tptr (Tqualified QC Tint); Tulong])) := eq_refl.
  Succeed Example _0 : TEST "integral" (Nglobal $ Nid "integral") := eq_refl.
  Succeed Example _0 : TEST "f<int>(int, int)" (Ninst (Nglobal $ Nfunction function_qualifiers.N "f" [Tint; Tint]) [Atype Tint]) := eq_refl.
  Succeed Example _0 : TEST "f<int>(#e1, const #e2)" (Ninst (Nglobal $ Nfunction function_qualifiers.N "f" [Tenum (Nglobal (Nid "e1")); Tconst $ Tenum (Nglobal (Nid "e2"))]) [Atype Tint]) := eq_refl.
  Succeed Example _0 : TEST "f(int[], int[3])" (Nglobal $ Nfunction function_qualifiers.N "f" [Tincomplete_array Tint; Tarray Tint 3]) := eq_refl.
  Succeed Example _0 : TEST "f(const volatile int[], int[3])" (Nglobal $ Nfunction function_qualifiers.N "f" [Tincomplete_array (Tqualified QCV Tint); Tarray Tint 3]) := eq_refl.
  Succeed Example _0 : TEST "f(void)" (Nglobal $ Nfunction function_qualifiers.N "f" []) := eq_refl.
  Succeed Example _0 : TEST "::f(void)" (Nglobal $ Nfunction function_qualifiers.N "f" []) := eq_refl.
  Succeed Example _0 : TEST "operator """"_f(enum ::foo)" (Nglobal $ Nop_lit "f" [Tenum $ Nglobal $ Nid "foo"]) := eq_refl.

  Succeed Example _0 : TEST "submit(unsigned long, std::function<void()>)"
                 (Nglobal
                    (Nfunction function_qualifiers.N "submit"
                       [Tnum int_rank.Ilong Unsigned; Tnamed (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "function")) [Atype (Tfunction (FunctionType Tvoid []))])])) := eq_refl.
  Succeed Example _0 : TEST "submit(unsigned long, std::function<void(long, int, ...)>)"
                         (Nglobal
                            (Nfunction function_qualifiers.N "submit"
                               [Tnum int_rank.Ilong Unsigned; Tnamed (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "function")) [Atype (Tfunction (FunctionType (ft_arity:=Ar_Variadic) Tvoid [Tlong; Tint]))])])) := eq_refl.

  Succeed Example _0 : TEST "::f(enum ::foo)" (Nglobal $ Nfunction function_qualifiers.N "f" [Tenum $ Nglobal $ Nid "foo"]) := eq_refl.
  Succeed Example _0 : TEST "::f(struct ::foo)" (Nglobal $ Nfunction function_qualifiers.N "f" [Tnamed $ Nglobal $ Nid "foo"]) := eq_refl.
  Succeed Example _0 : TEST "::f(class ::foo)" (Nglobal $ Nfunction function_qualifiers.N "f" [Tnamed $ Nglobal $ Nid "foo"]) := eq_refl.
  Succeed Example _0 : TEST "::f(::foo)" (Nglobal $ Nfunction function_qualifiers.N "f" [Tnamed $ Nglobal $ Nid "foo"]) := eq_refl.
  Succeed Example _0 : TEST "CpuSet::forall(void (*)(int)) const"
                 (Nscoped (Nglobal (Nid "CpuSet")) (Nfunction function_qualifiers.Nc "forall" [Tptr $ Tfunction (FunctionType Tvoid [Tint])])) := eq_refl.
  Succeed Example _0 : TEST "CpuSet::forall(void (C::*)(int)) const"
                         (Nscoped (Nglobal (Nid "CpuSet")) (Nfunction function_qualifiers.Nc "forall" [Tmember_pointer (Tnamed (Nglobal $ Nid "C")) $ Tfunction (FunctionType Tvoid [Tint])])) := eq_refl.

  Succeed Example _0 : TEST "CpuSet::forall(void (C::*)(int), ...) const"
                         (Nscoped (Nglobal (Nid "CpuSet")) (Nfunction function_qualifiers.Nc "forall" [Tmember_pointer (Tnamed (Nglobal $ Nid "C")) $ Tfunction (FunctionType Tvoid [Tint])])) := eq_refl.
  Succeed Example _0 : TEST "CpuSet::forall(void (C::*)(int, ...), ...) const"
                         (Nscoped (Nglobal (Nid "CpuSet")) (Nfunction function_qualifiers.Nc "forall" [Tmember_pointer (Tnamed (Nglobal $ Nid "C")) $ Tfunction (FunctionType (ft_arity:=Ar_Variadic) Tvoid [Tint])])) := eq_refl.

  Succeed Example _0 : TEST "foo(unsigned int128, int128)" (Nglobal (Nfunction function_qualifiers.N "foo" [Tuint128_t; Tint128_t])) := eq_refl.

  Succeed Example _0 : TEST "foo(unsigned, signed, char,unsigned char,signed char,short, short int, unsigned short, unsigned short int, signed short, signed short int, int, unsigned int, signed int, long, long int, unsigned long, unsigned long int, signed long, signed long int, long long, long long int, unsigned long long, unsigned long long int, signed long long, signed long long int)" (Nglobal (Nfunction function_qualifiers.N "foo" [Tuint;Tint;Tchar; Tuchar; Tschar; Tshort; Tshort; Tushort; Tushort; Tshort; Tshort; Tint; Tuint; Tint; Tlong; Tlong; Tulong; Tulong; Tlong; Tlong; Tlonglong; Tlonglong;Tulonglong;Tulonglong;Tlonglong;Tlonglong])) := eq_refl.

  Succeed Example _0 : TEST "foo(char8_t, char16_t, char32_t, wchar_t, char)" (Nglobal (Nfunction function_qualifiers.N "foo" [Tchar8_t; Tchar16_t; Tchar32_t; Twchar_t; Tchar])) := eq_refl.

  Succeed Example _0 : TEST "submit(unsigned long, std::function<void()>)"
                         (Nglobal
        (Nfunction function_qualifiers.N "submit"
           [Tnum int_rank.Ilong Unsigned; Tnamed (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "function")) [Atype (Tfunction (FunctionType Tvoid []))])])) := eq_refl.
  Succeed Example _0 : TEST "submit(unsigned long, std::function<void(long, int, ...)>)"
                         (Nglobal
         (Nfunction function_qualifiers.N "submit"
            [Tnum int_rank.Ilong Unsigned; Tnamed (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "function")) [Atype (Tfunction (FunctionType (ft_arity:=Ar_Variadic) Tvoid [Tlong; Tint]))])])) := eq_refl.

  Succeed Example _0 : TEST "foo(int(int))" (Nglobal (Nfunction function_qualifiers.N "foo" [Tfunction (FunctionType Tint [Tint])])) := eq_refl.
  Succeed Example _0 : TEST "foo(int(*)(int))" (Nglobal (Nfunction function_qualifiers.N "foo" [Tptr $ Tfunction (FunctionType Tint [Tint])])) := eq_refl.
  Succeed Example _0 : TEST "foo(int(const *)(int))" (Nglobal (Nfunction function_qualifiers.N "foo" [Tptr $ Tconst $ Tfunction (FunctionType Tint [Tint])])) := eq_refl.
  Succeed Example _0 : TEST "foo(int(*const)(int))" (Nglobal (Nfunction function_qualifiers.N "foo" [Tconst $ Tptr $ Tfunction (FunctionType Tint [Tint])])) := eq_refl.
  Succeed Example _0 : TEST "foo(int(C::*)(int))" (Nglobal (Nfunction function_qualifiers.N "foo" [Tmember_pointer (Tnamed $ Nglobal (Nid "C")) $ Tfunction (FunctionType Tint [Tint])])) := eq_refl.

  Succeed Example _0 : TEST_type "enum E()" (Tfunction (FunctionType (Tenum (Nglobal (Nid "E"))) [])) := eq_refl.
  Succeed Example _0 : TEST_type "enum NS::E()" (Tfunction (FunctionType (Tenum (Nscoped (Nglobal (Nid "NS")) (Nid "E"))) [])) := eq_refl.

  Succeed Example _0 : TEST "C<1b, 0b>" (Ninst (Nglobal (Nid "C")) [Avalue (Eint 1 Tbool); Avalue (Eint 0 Tbool)]) := eq_refl.
  Succeed Example _0 : TEST "C<1, 0>" (Ninst (Nglobal (Nid "C")) [Avalue (Eint 1 Tint); Avalue (Eint 0 Tint)]) := eq_refl.
  Succeed Example _0 : TEST "C<'a', '\t'>" (Ninst (Nglobal (Nid "C")) [Avalue (Echar 97 Tchar); Avalue (Echar 9 Tchar)]) := eq_refl.

  Succeed Example _0 : TEST "C<1, ...<int, long>>" (Ninst (Nglobal (Nid "C")) [Avalue (Eint 1 Tint); Apack [Atype Tint; Atype Tlong]]) := eq_refl.
  Succeed Example _0 : TEST "C<1, ...<int, long>>" (Ninst (Nglobal (Nid "C")) [Avalue (Eint 1 Tint); Apack [Atype Tint; Atype Tlong]]) := eq_refl.

  Succeed Example _0 : TEST "C<template C>" (Ninst (Nglobal (Nid "C")) [Atemplate (Nglobal (Nid "C"))]) := eq_refl.
  Succeed Example _0 : TEST "C<template C::CC>" (Ninst (Nglobal (Nid "C")) [Atemplate (Nscoped (Nglobal (Nid "C")) (Nid "CC"))]) := eq_refl.

  Succeed Example _0 : TEST_fail "C::~D()" := eq_refl.
  Succeed Example _0 : TEST_fail "C::~C(int)" := eq_refl.
  Succeed Example _0 : TEST "C::~C()" (Nscoped (Nglobal (Nid "C")) Ndtor) := eq_refl.

  Succeed Example _0 : TEST "foo(typename $T)" (Nglobal (Nfunction function_qualifiers.N "foo" [Tparam "T"])) := eq_refl.
  Succeed Example _0 : TEST "foo(typename $T::nested)" (Nglobal (Nfunction function_qualifiers.N "foo" [Tnamed (Nscoped (Ndependent (Tparam "T")) (Nid "nested"))])) := eq_refl.

  (* known issues *)

  (* NOTE: non-standard names *)
  Succeed Example _0 : TEST "Msg::@msg" (Nscoped Msg (Nfirst_decl "msg")) := eq_refl.
  Succeed Example _0 : TEST "Msg::.msg" (Nscoped Msg (Nfirst_child "msg")) := eq_refl.
  Succeed Example _0 : TEST "typename foo" (Ndependent (Tnamed (Nglobal (Nid "foo")))) := eq_refl.
  Succeed Example _0 : TEST "typename foo<int>::type"
                 (Ndependent (Tnamed (Nscoped (Ninst (Nglobal (Nid "foo")) [Atype Tint]) (Nid "type")))) := eq_refl.
  Succeed Example _0 : TEST "::f(#::foo)" (Nglobal $ Nfunction function_qualifiers.N "f" [Tenum $ Nglobal $ Nid "foo"]) := eq_refl.
  Succeed Example _0 : TEST "Msg<int& &&>" (Ninst (Nglobal (Nid "Msg")) [Atype (Trv_ref (Tref Tint))]) := eq_refl.

  Succeed Example _0 : TEST "Msg<`name>" (Ninst (Nglobal (Nid "Msg")) [Avalue (Eparam "name")]) := eq_refl.

End TESTS.
