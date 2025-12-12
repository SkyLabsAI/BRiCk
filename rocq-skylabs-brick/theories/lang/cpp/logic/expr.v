(*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(**
 * Semantics of expressions
 * (expressed in weakest pre-condition style)
 *)
Require Import bluerock.prelude.numbers.
Require Import iris.proofmode.tactics.

Require Import bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.semantics.
Require Import bluerock.lang.cpp.logic.pred.
Require Import bluerock.lang.cpp.logic.path_pred.
Require Import bluerock.lang.cpp.logic.heap_pred.
Require Import bluerock.lang.cpp.logic.raw.
Require Import bluerock.lang.cpp.logic.const.
Require Import bluerock.lang.cpp.logic.operator.
Require Import bluerock.lang.cpp.logic.destroy.
Require Import bluerock.lang.cpp.logic.initializers.
Require Import bluerock.lang.cpp.logic.wp.
Require Import bluerock.lang.cpp.logic.call.
Require Import bluerock.lang.cpp.logic.core_string.
Require Import bluerock.lang.cpp.logic.translation_unit.
Require Import bluerock.lang.cpp.logic.dispatch.
Require Import bluerock.lang.cpp.logic.func.
Require Import bluerock.iris.extra.bi.errors.

Module Type Expr.
  (* Needed for [Unfold wp_test] *)
  #[local] Arguments wp_test [_ _ _ _] _ _ _.
  #[local] Open Scope free_scope.

  (**
   * Weakest pre-condition for expressions

     NOTE It is important that these rules are sound, but less important that
     they are complete. When in doubt, we err on the side of caution and under-specify
     the behavior of various constructs.

     If you run into code that requires addditional semantic specification, please file
     an issue.

     NOTE Since [wp_operand] can be used to prove [wp_init] but not vice-versa, we
          use [wp_operand] to specify the semantics of any expression that is guaranteed
          to return a primitive.
   *)

  Section with_resolve.
    Context `{Σ : cpp_logic} {resolve:genv}.
    Variables (tu : translation_unit) (ρ : region).

    #[local] Notation wp_lval := (wp_lval tu ρ).
    #[local] Notation wp_xval := (wp_xval tu ρ).
    #[local] Notation wp_init := (wp_init tu ρ).
    #[local] Notation wp_operand := (wp_operand tu ρ).
    #[local] Notation wp_initialize := (wp_initialize tu ρ).
    #[local] Notation wp_test := (wp_test tu ρ).
    #[local] Notation wp_discard := (wp_discard tu ρ).
    #[local] Notation wp_glval := (wp_glval tu ρ).
    #[local] Notation wp_args := (wp_args tu ρ).
    #[local] Notation interp := (interp tu).
    (* TODO Fix these *)
    #[local] Notation wp_fptr := (wp_fptr resolve.(genv_tu).(types)).
    #[local] Notation wp_mfptr := (wp_mfptr resolve.(genv_tu).(types)).

    #[local] Notation size_of := (@size_of resolve) (only parsing).

    (* enumeration constants are prvalues *)
    Axiom wp_operand_enum_const : forall gn id e Q,
      (**
      TODO (FM-4393): The type <<t>> in <<Gconstant t>> now redundant.
      *)
      tu.(types) !! Nenum_const gn id = Some (Gconstant (Tenum gn) (Some e)) ->
          (* evaluation of the expression does not get access to
             local variables, so it gets [Remp] rather than [ρ].
             In addition, the evaluation is done at compile-time, so we clean
             up the temporaries eagerly. *)
          WPE.wp_operand tu (Remp None None (Tenum gn)) e (fun v frees => interp frees $ Q v FreeTemps.id)
      |-- wp_operand (Eenum_const gn id) Q.

    (* integer literals are prvalues *)
    Axiom wp_operand_int : forall n ty Q,
      [! has_type_prop (Vint n) (drop_qualifiers ty) !] //\\ Q (Vint n) FreeTemps.id
      |-- wp_operand (Eint n ty) Q.

    (* NOTE: character literals represented in the AST as 32-bit unsigned integers
             (with the Coq type [N]). We assume that the AST is well-typed so the
             value here will be well-typed according to the character type.
     *)
    Axiom wp_operand_char : forall c cty Q,
          Q (Vchar c) FreeTemps.id
      |-- wp_operand (Echar c (Tchar_ cty)) Q.

    (* boolean literals are prvalues *)
    Axiom wp_operand_bool : forall (b : bool) Q,
          Q (Vbool b) FreeTemps.id
      |-- wp_operand (Ebool b) Q.

    (** * String Literals

        The standard states <https://eel.is/c++draft/lex.string#9>:

            | Evaluating a string-literal results in a string literal object with
            | static storage duration ([basic.stc]). Whether all string-literals
            | are distinct (that is, are stored in nonoverlapping objects) and whether
            | successive evaluations of a string-literal yield the same or a different
            | object is unspecified.
            |
            | [Note 4: The effect of attempting to modify a string literal object is
            | undefined. — end note]

        which means the C++ abstract machine manages ownership of string literals
        during its lifetime, handing out read-access to the underlying memory when
        necessary - in an implementation-defined way.

        We treat this in our logic by granting a pair of resources
        each time a string literal is evaluated:

        1. a read-only (fraction < 1) of memory containing the string, and
        2. a destroyer which can be used to give the values back to
           the abstract machine.

        Note that the pointer `p` is universally quantified. This follows
        the standard which does *not* guarantee that successive evaluations
        of the same string literal will return the same pointer
        (in practice, this generally only occurs when there are multiple
         translation units involved).

        Note that the fancy update is necessary to support a model where
        the string pool is maintained within an invariant of the abstract
        machine.
     *)
    Axiom wp_lval_string : forall chars ct Q,
          (Forall (p : ptr) (q : Qp),
            p |-> string_bytesR ct q$c chars -*
            □ (Forall q', (p |-> string_bytesR ct q'$c chars ={⊤}=∗ emp)) -*
            Q p FreeTemps.id)
      |-- wp_lval (Estring chars (Tchar_ ct)) Q.

    (** The value for the corresponding character literal.

        Because characters are represented uniformly as [N] within the syntax,
        special handling is necessary for the types <<signed char>> and <<unsigned char>>
        which are both represented using [Vint].

        The injection for <<unsigned char>> is trivial, but for <<signed char>>
        we effectively interpret the value as an <<unsigned char>> and use
        the casting logic to cast it to a <<signed char>>.
     *)
    Definition char_literal (char_type : type) : option (N -> val) :=
      match char_type with
      | Tchar_ _ => Some $ fun n => Vchar n
      | Tnum int_rank.Ichar Unsigned => Some $ fun n => Vint $ Z.of_N n
      | Tnum int_rank.Ichar Signed =>
          let bits := bitsize.bitsN $ int_rank.bitsize int_rank.Ichar in
          Some $ fun n => Vint $ of_char bits Unsigned bits Signed n
      | _ => None
      end.

    (* The contents of an array initialized by a string literal with the given values.
       The [ls] does *not* contain the trailing <<NULL>> value. *)
    Definition fit_to_array (sz : N) (ls : list N) : option (list N) :=
      if bool_decide (sz <= lengthN ls)%N
      then None (* the string must fit in the array: <https://eel.is/c++draft/dcl.init.string#2> *)
      else Some $ ls ++ replicateN (sz - lengthN ls)%N 0%N.

    (* Most string literals contain characters, but <<unsigned char>> and
       <<signed char>> are integral types and are therefore represented
       using [Vint].

       For character literals, Clang inserts an explicit cast, i.e. [Cintegral ..],
       but for string literals that cast is implicit.
     *)
    Axiom wp_init_string : forall (into : ptr) len chars ct Q,
          (let (cv,ct) := decompose_type ct in
           match fit_to_array len $ literal_string.to_list_N chars , char_literal ct with
           | Some values , Some to_val =>
               let q := cQp.mk (q_const cv) 1 in
               ([∗list] i ↦ n ∈ values,
                 into .[ ct ! i ] |-> primR ct q (to_val n)) -*
               into |-> type_ptrR (Tarray ct len) -*
               Q FreeTemps.id
           | _ , _ => False
           end)
      |-- wp_init (Tarray ct len) into (Estring chars ct) Q.

    (* `this` is a prvalue *)
    Axiom wp_operand_this : forall ty Q,
          valid_ptr (_this ρ) ** Q (Vptr $ _this ρ) FreeTemps.id
      |-- wp_operand (Ethis ty) Q.

    (* [read_decl p t Q] "returns" the reference referred to by
       the pointer [p] when the declaration has type [t]. If the resulting value
       is [r], then [has_type (Vref r) (Tref $ drop_references t)].

       This logic encapsulates the handling of globals, locals, and members
       that have reference type. In this case, the reference being returned
       is the one that the reference location points to. If the location's
       type is not a reference, then the pointer is returned *after* it is
       checked to be strictly valid.
     *)
    Definition read_decl (p : ptr) (t : type) (Q : ptr -> mpred) :=
      match drop_qualifiers t with
      | Tref ty
      | Trv_ref ty =>
          Exists r,
          (Exists q, p |-> primR (Tref $ erase_qualifiers ty) q (Vref r) ** True) //\\ Q r
          (* The rules for [primR] guarantee [reference_to ty r] *)
      | _ => reference_to (erase_qualifiers t) p ** Q p
      end.

    (* variables and global object references are lvalues *)
    Axiom wp_lval_var : forall ty x Q,
          read_decl (_local ρ x) ty (fun p => Q p FreeTemps.id)
      |-- wp_lval (Evar x ty) Q.
    Axiom wp_lval_global : forall ty x Q,
          read_decl (_global x) ty (fun p => Q p FreeTemps.id)
      |-- wp_lval (Eglobal x ty) Q.

    (* [Eglobal_member (Nscoped cls nm)] represents a member pointer
       on class [cls] to member [nm]. It is always a pr-value.
     *)
    Axiom wp_operand_global_member : forall ty cls nm Q,
          Q (Vmember_ptr cls $ Some nm) FreeTemps.id
      |-- wp_operand (Eglobal_member (Nscoped cls nm) ty) Q.

    Definition read_arrow (arrow : bool) (e : Expr) (Q : ptr -> FreeTemps.t -> mpred) : mpred :=
      (if arrow then
         match unptr $ drop_qualifiers $ type_of e with
         | Some t =>
             letI* base, free := wp_operand e in
             match base with
             | Vptr p => reference_to (erase_qualifiers t) p ** Q p free
             | _ => False
             end
         | _ => False
         end
       else
         wp_glval e Q)%I.

    Lemma read_arrow_frame arrow e Q Q' :
      Forall p free, Q p free -* Q' p free
      |-- read_arrow arrow e Q -* read_arrow arrow e Q'.
    Proof.
      rewrite /read_arrow.
      iIntros "K".
      case_match.
      { case_match; try iIntros "[]".
        iApply wp_operand_frame. reflexivity.
        iIntros (??); case_match; eauto.
        iIntros "[$ X]"; iApply "K"; iApply "X". }
      { iApply wp_glval_frame; eauto. reflexivity. }
    Qed.

    Definition arrow_aggregate_type (arrow : bool) (t : decltype) : option (ValCat * type_qualifiers * name) :=
      if arrow then
        match drop_qualifiers t with
        | Tptr pt =>
            match decompose_type pt with
            | (cv, Tnamed n) => Some (Lvalue, cv, n)
            | _ => None
            end
        | _ => None
        end
      else
        let '(vc, et) := decltype.to_exprtype t in
        if bool_decide (vc = Prvalue)
        then None
        else
          match decompose_type et with
          | (cv, Tnamed nm) => Some (vc, cv, nm)
          | _ => None
          end.

    (* [Emember a f mut ty] is an lvalue by default except when
     * - where [m] is a member enumerator or a non-static member function, or
     * - where [a] is an rvalue and [m] is a non-static data member of non-reference type
     *)
    Axiom wp_lval_member : forall arrow ty a m mut vc cv nm Q,
        arrow_aggregate_type arrow (decltype_of_expr a) = Some (vc, cv, nm) ->
          (letI* base, free := read_arrow arrow a in
          letI* p := read_decl (base ,, _field (Field nm m)) ty in
          Q p free)
      |-- wp_lval (Emember arrow a m mut ty) Q.

    (* [Emember a m mut ty] is an xvalue if
     * - [a] is an rvalue and [m] is a non-static data member of non-reference type
     *)
    Axiom wp_xval_member : forall ty a m mut cv nm Q,
        arrow_aggregate_type false (decltype_of_expr a) = Some (Xvalue, cv, nm) ->
          match decltype.to_valcat ty with
          | Prvalue =>
            letI* base, free := wp_xval a in
            letI* p := read_decl (base ,, _field (Field nm m)) ty in
            Q p free
          | _ => False
          end
      |-- wp_xval (Emember false a m mut ty) Q.
    (* <<e->f>> is never an xvalue because <<e>> must be a pointer *)

    (**
       [Emember_ignore arrow obj e] represents:
       - <<obj->e>> if <<arrow = true>>, or
       - <<obj.e>> if <<arrow = false>>
       in both cases, <<e>> is a global object, e.g. [Eenum_const] or [Eglobal].
       The <<obj>> argument is evaluated but the value is not consumed.
     *)

    Definition wp_ignore_obj (arrow : bool) (e : Expr) (Q : FreeTemps.t -> mpred) : mpred :=
      read_arrow arrow e (fun _ => Q).

    Axiom wp_operand_member_ignore : forall arrow obj e Q,
            (letI* free1 := wp_ignore_obj arrow obj in
             letI* v , free2 := wp_operand e in
             Q v (free2 >*> free1))
        |-- wp_operand (Emember_ignore arrow obj e) Q.

    Axiom wp_lval_member_ignore : forall arrow obj e Q,
        (letI* free1 := wp_ignore_obj arrow obj in
         letI* p , free2 := wp_lval e in
         Q p (free2 >*> free1))
     |-- wp_lval (Emember_ignore arrow obj e) Q.

    Axiom wp_xval_member_ignore : forall arrow obj e Q,
        (letI* free1 := wp_ignore_obj arrow obj in
         letI* p , free2 := wp_lval e in
         Q p (free2 >*> free1))
    |-- wp_xval (Emember_ignore arrow obj e) Q.

    (** *** Subscripting
        The BRiCk semantics *directly* supports subscripting on array types in
        order to make value category computation composable. Because of this,
        the "pointer" arguments to [Esubscript] can be any of:
        - a pointer (of value category Prvalue)
        - any array type (of value category GLvalue)
     *)

    Definition subscript_scheme (e1 e2 : Expr) : option (bool * ValCat * type) :=
      let array_type :=
        qual_norm (fun cv ty =>
            match ty with
            | Tarray ety _
            | Tincomplete_array ety
            | Tvariable_array ety _ => Some $ tqualified cv ety
            | _ => mfail
            end)
      in
      let guard_arithmetic ty v := if is_arithmetic ty then v else None in
      match drop_qualifiers $ decltype_of_expr e1 , drop_qualifiers $ decltype_of_expr e2 with
      | Tref aty , ity => guard_arithmetic ity $ (fun t => (true, Lvalue, t)) <$> array_type aty
      | Trv_ref aty , ity => guard_arithmetic ity $ (fun t => (true, Xvalue, t)) <$> array_type aty
      | Tptr ety , ity => guard_arithmetic ity $ Some (true, Prvalue, ety)
      | ity , Tref aty => guard_arithmetic ity $ (fun t => (false, Lvalue, t)) <$> array_type aty
      | ity , Trv_ref aty => guard_arithmetic ity $ (fun t => (false, Xvalue, t)) <$> array_type aty
      | ity , Tptr ety => guard_arithmetic ity $ Some (false, Prvalue, ety)
      | _ , _ => None
      end.

    Definition wp_ptr (vc : ValCat) (e : Expr) (Q : ptr -> FreeTemps.t -> epred) : mpred :=
      match vc with
      | Prvalue => wp_operand e $ fun v free => Exists p, [| v = Vptr p |] ** Q p free
      | Lvalue => wp_lval e Q
      | Xvalue => wp_xval e Q
      end.

    Lemma wp_ptr_frame vc e Q Q' :
      Forall p free, Q p free -* Q' p free |-- wp_ptr vc e Q -* wp_ptr vc e Q'.
    Proof.
      rewrite /wp_ptr.
      case_match; iIntros "X";
        [ iApply wp_lval_frame
        | iApply wp_operand_frame
        | iApply wp_xval_frame ]; try reflexivity; eauto.
      { iIntros (??) "Y"; iDestruct "Y" as (?) "[% Y]".
        iExists _; iFrame "%". iApply "X"; eauto. }
    Qed.

    (* TOOD: This should be extended to support [Vchar] when <<e>> is a
       character type. In this case, the result should be the result of
       integral promotion.
     *)
    Definition wp_int (e : Expr) (Q : Z -> FreeTemps.t -> epred) : mpred :=
      letI* v, free := wp_operand e in
      Exists z, [| v = Vint z |] ** Q z free.

    Lemma wp_int_frame e Q Q' :
      Forall p free, Q p free -* Q' p free |-- wp_int e Q -* wp_int e Q'.
    Proof.
      rewrite /wp_int.
      iIntros "X"; iApply wp_operand_frame; try reflexivity.
      { iIntros (??) "Y"; iDestruct "Y" as (?) "[% Y]".
        iExists _; iFrame "%". iApply "X"; eauto. }
    Qed.

    (* [Esubscript e i _] when one operand is an array lvalue or pointer.
     * Technically, [vc] is not permitted to be [Xvalue] in this rule.
     *)
    Axiom wp_lval_subscript : forall e side vc i t Q,
      subscript_scheme e i = Some (side, vc, t) ->
      (if side then
         let* '(base, idx), free := nd_seq (wp_ptr vc e) (wp_int i) in
         let addr := base .[ erase_qualifiers t ! idx ] in
         reference_to t addr ** Q addr free
       else
         let* '(idx, base), free := nd_seq (wp_int e) (wp_ptr vc i) in
         let addr := base .[ erase_qualifiers t ! idx ] in
         reference_to t addr ** Q addr free)
      |-- wp_lval (Esubscript e i t) Q.

    (* [Esubscript e i _] when one operand is an array xvalue
     *)
    Axiom wp_xval_subscript : forall e side i t Q,
        subscript_scheme e i = Some (side, Xvalue, t) ->
        (if side then
           let* '(base, idx), free := nd_seq (wp_xval e) (wp_int i) in
           let addr := base .[ erase_qualifiers t ! idx ] in
           reference_to t addr ** Q addr free
         else
           let* '(idx, base), free := nd_seq (wp_int e) (wp_xval i) in
           let addr := base .[ erase_qualifiers t ! idx ] in
           reference_to t addr ** Q addr free)
      |-- wp_xval (Esubscript e i t) Q.

    (** * Unary Operators
     *)

    (** The `*` operator is an lvalue, but this does not perform an access yet
        (see [wp_operand_cast_l2r] instead).

        We check pointer [p] is strictly valid and aligned.
        The standard says (<https://eel.is/c++draft/expr.unary.op#1>?):

        > The unary * operator performs indirection: the expression to which it is applied
        > shall be a pointer to an object type, or a pointer to a function type and the
        > result is an lvalue referring to the object or function to which the expression
        > points. If the type of the expression is “pointer to T”, the type of the result
        > is “T”.

        "The object or function" means we must require at least strict validity
        (to exclude null and past-the-end pointers).
        We don't ask for [type_ptrR]: that would (unnecessarily?) forbid code like:
        <<
        struct A { int x; int *y{&*x}; };
        >>
     *)
    Axiom wp_lval_deref : forall ty e Q,
        wp_operand e (fun v free =>
                      match v with
                      | Vptr p =>
                        (* This side-condition is not redundant for [&*p].
                           [aligned_ofR] should be implied by the fact
                           that the pointer [v] is well typed. *)
                        reference_to (erase_qualifiers ty) p **
                        Q p free
                      | _ => False
                      end)
        |-- wp_lval (Ederef e ty) Q.

    (** the `&` operator

        https://eel.is/c++draft/expr.unary.op#3
     *)
    Axiom wp_operand_addrof : forall e Q,
            wp_lval e (fun p free => Q (Vptr p) free)
        |-- wp_operand (Eaddrof e) Q.

    (** "pure" unary operators on primitives, e.g. `-`, `!`, etc.

        NOTE this rule assumes that [eval_unop] is deterministic.
     *)
    Axiom wp_operand_unop : forall o e ty Q,
        wp_operand e (fun v free => (* todo: rval? *)
          Exists v',
          [| eval_unop tu o (drop_qualifiers (type_of e)) (drop_qualifiers ty) v v' |] **
          Q v' free)
        |-- wp_operand (Eunop o e ty) Q.

    (* The semantics of pre- and post- increment/decrement.

       NOTE: This function assumes that [ty1] is the LHS and that the result will
             that type.
     *)
    Definition inc_dec_op (op : BinOp) (ty : type) (v : val) : val -> mpred :=
      if is_arithmetic ty then
        match promote_integral tu ty with
        | Some ity => fun v_result =>
            Exists v' v'',
              [| conv_int tu ty ity v v' |] **
              eval_binop tu op ity ity ity v' (Vint 1) v'' **
              [| conv_int tu ity ty v'' v_result |]
        | None => fun _ => UNSUPPORTED ""
        end
      else if is_pointer ty then
            (* use eval_binop_impure *)
             fun v_result => eval_binop tu op ty Tint ty v (Vint 1) v_result
      else fun _ => UNSUPPORTED "cast-op".

    Definition pre_op (b : BinOp) (ty : type) (e : Expr) (Q : ptr -> FreeTemps.t -> mpred) : mpred :=
      let ety := erase_qualifiers $ type_of e in
      wp_lval e (fun a free => Exists v v',
                   (inc_dec_op b ety v v' ** True) //\\
                   (a |-> primR ety 1$m v **
                      (a |-> primR ety 1$m v' -* Q a free))).

    (** `++e`
        https://eel.is/c++draft/expr.pre.incr#1
     *)
    Axiom wp_lval_preinc : forall e ty Q,
        pre_op Badd ty e Q |-- wp_lval (Epreinc e ty) Q.

    (** `--e`
        https://eel.is/c++draft/expr.pre.incr#2
     *)
    Axiom wp_lval_predec : forall e ty Q,
        pre_op Bsub ty e Q |-- wp_lval (Epredec e ty) Q.

    Definition post_op (b : BinOp) (ty : type) (e : Expr) (Q : val -> FreeTemps.t -> mpred) : mpred :=
      let ety := erase_qualifiers $ type_of e in
      wp_lval e (fun a free => Exists v v',
                   (inc_dec_op b ety v v' ** True) //\\
                   (a |-> primR ety 1$m v **
                      (a |-> primR ety 1$m v' -* Q v free))).

    (** `e++`
        https://eel.is/c++draft/expr.post.incr#1
     *)
    Axiom wp_operand_postinc : forall e ty Q,
        post_op Badd ty e Q |-- wp_operand (Epostinc e ty) Q.

    (** `e--`
        https://eel.is/c++draft/expr.post.incr#2
     *)
    Axiom wp_operand_postdec : forall e ty Q,
        post_op Bsub ty e Q |-- wp_operand (Epostdec e ty) Q.

    (** * Binary Operators *)
    (* NOTE the following axioms assume that [eval_binop] is deterministic *)
    Axiom wp_operand_binop : forall o e1 e2 ty Q,
        nd_seq (wp_operand e1) (wp_operand e2) (fun '(v1,v2) free =>
          Exists v',
            (eval_binop tu o
                (drop_qualifiers (type_of e1)) (drop_qualifiers (type_of e2))
                (drop_qualifiers ty) v1 v2 v' ** True) //\\
            Q v' free)
        |-- wp_operand (Ebinop o e1 e2 ty) Q.

    (* NOTE the right operand is sequenced before the left operand since
       P0145R3 (C++17).
     *)
    Axiom wp_lval_assign : forall ty l r Q,
        (letI* '(la, rv), free :=
           eval2 (evaluation_order.order_of OOEqual) (wp_lval l) (wp_operand r) in
            la |-> anyR (erase_qualifiers ty) 1$m **
           (la |-> tptstoR (erase_qualifiers ty) 1$m rv -* Q la free))
        |-- wp_lval (Eassign l r ty) Q.

    Axiom wp_lval_bop_assign : forall ty o l r Q,
            match convert_type_op tu o (type_of l) (type_of r) with
            | Some (tl, tr, resultT) =>
              letI* '(la, rv), free :=
                eval2 (evaluation_order.order_of OOEqual) (wp_lval l) (wp_operand r) in
              Exists v cv v',
                    ((* cast and perform the computation *)
                      [| convert tu (type_of l) tl v cv |] **
                      [| (* ensured by the AST *) tr = type_of r |] **
                      eval_binop tu o tl tr resultT cv rv v' **
                        (* convert the value back to the target type so it can be stored *)
                        [| convert tu resultT ty cv v' |] ** True) //\\
                    (la |-> primR (erase_qualifiers ty) 1$m v **
                      (la |-> primR (erase_qualifiers ty) 1$m v' -* Q la free))
            | _ => False%I
            end
        |-- wp_lval (Eassign_op o l r ty) Q.

    (** The comma operator can be both an lvalue and a prvalue
        depending on what the second expression is.

        `a, b` runs `a`, discards the value (but does not clean it up yet),
        then runs `b`. the value (and temporaries) of `a` are destroyed
        after `b` completes (usually at the end of the statement).
     *)
    Axiom wp_lval_comma : forall e1 e2 Q,
        wp_discard e1 (fun free1 => wp_lval e2 (fun val free2 => Q val (free2 >*> free1)))
        |-- wp_lval (Ecomma e1 e2) Q.

    Axiom wp_xval_comma : forall e1 e2 Q,
        wp_discard e1 (fun free1 => wp_xval e2 (fun val free2 => Q val (free2 >*> free1)))
        |-- wp_xval (Ecomma e1 e2) Q.

    Axiom wp_operand_comma : forall e1 e2 Q,
        wp_discard e1 (fun free1 => wp_operand e2 (fun val free2 => Q val (free2 >*> free1)))
        |-- wp_operand (Ecomma e1 e2) Q.

    Axiom wp_init_comma : forall ty p e1 e2 Q,
        wp_discard e1 (fun free1 => wp_init ty p e2 (fun free2 => Q (free2 >*> free1)))
        |-- wp_init ty p (Ecomma e1 e2) Q.

    (** short-circuting operators *)
    Axiom wp_operand_seqand : forall e1 e2 Q,
        Unfold WPE.wp_test (wp_test e1 (fun c free1 =>
        (* ^ note: technically an rvalue, but it must be a primitive,
           otherwise there will be an implicit cast to bool, to it is
           always an rvalue *)
           if c
           then wp_test e2 (fun c free2 => (* see comment above *)
                              Q (Vbool c) (free2 >*> free1))
           else Q (Vbool c) free1))
        |-- wp_operand (Eseqand e1 e2) Q.

    Axiom wp_operand_seqor : forall e1 e2 Q,
        Unfold WPE.wp_test (wp_test e1 (fun c free1 =>
        (* ^ note: technically an rvalue, but it must be a primitive,
           otherwise there will be an implicit cast to bool, to it is
           always an rvalue *)
           if c
           then Q (Vbool c) free1
           else wp_test e2 (fun c free2 => (* see comment above *)
                              Q (Vbool c) (free2 >*> free1))))
        |-- wp_operand (Eseqor e1 e2) Q.

    (** * Casts
        Casts apply exclusively to primitive types, all other casts in C++
        are represented as overloaded functions.
     *)

    (** [Cl2r] represents reads of locations.
    This counts as an _access_, so it must happen at one of the types listed in
    https://eel.is/c++draft/basic.lval#11.
    *)
    Axiom wp_operand_cast_l2r : forall e Q,
        (
          letI* a, free := wp_glval e in
          Exists v,
          (Exists q, a |-> initializedR (erase_qualifiers $ type_of e) q v ** True) //\\
          Q v free
        ) |-- wp_operand (Ecast Cl2r e) Q.

    Lemma wp_operand_cast_l2r_prim e Q :
        (
          letI* a, free := wp_glval e in
          Exists v,
          (Exists q, a |-> primR (erase_qualifiers $ type_of e) q v ** True) //\\
          Q v free
        ) |-- wp_operand (Ecast Cl2r e) Q.
    Proof.
      intros. rewrite -wp_operand_cast_l2r. iIntros "wp".
      iApply (wp_glval_wand with "wp"). iIntros (p f) "?".
      iStopProof. f_equiv; intro. f_equiv. f_equiv; intro.
      f_equiv. rewrite _at_primR _at_initializedR.
      iIntros "(_ & $ & $)".
    Qed.

    Lemma wp_operand_cast_l2r_raw : forall (e : Expr) Q,
        type_of e = Tuchar ->
        (letI* a, free := wp_glval e in
         Exists r,
         (Exists q, a |-> rawR q r ** True) //\\ Q (Vraw r) free)
      |-- wp_operand (Ecast Cl2r e) Q.
    Proof.
      intros. rewrite -wp_operand_cast_l2r /=. iIntros "wp".
      iApply (wp_glval_wand with "wp"). iIntros (p f) "(%r & H)".
      iExists (Vraw r). rewrite H.
      iStopProof. f_equiv. f_equiv; intro. f_equiv.
      iIntros "X".
      iDestruct (observe (has_type _ _) with "X" ) as "#?".
      rewrite rawR.unlock initializedR.unlock _at_sep _at_pureR /=.
      iFrame "∗#".
    Qed.

    (** No-op casts [Cnoop] are casts that only affect the type and not the value.
        Clang states that these casts are only used for adding and removing [const].
     *)

    (*
    Casts that occur in initialization expressions.
    Since object has not truly been initialized yet, the [const]ness can change.
    *)
    Variant noop_cast_type : Set :=
    | AddConst    (_ : type)
    | RemoveConst (_ : type)
    | Nothing. (* a real no-op *)

    Definition classify_cast (from to : type) : option noop_cast_type :=
      let '(from_cv, from_ty) := decompose_type from in
      let '(to_cv, to_ty) := decompose_type to in
      if bool_decide (erase_qualifiers from_ty = erase_qualifiers to_ty) then
        if bool_decide (from_cv = to_cv) then
          Some Nothing
        else if bool_decide (from_cv = merge_tq QC to_cv) then
               Some (RemoveConst from_ty)
             else if bool_decide (to_cv = merge_tq QC from_cv) then
                    Some (AddConst to_ty)
                  else None
      else None. (* conservatively fail *)

    Record unsupported_init_noop_cast (e : Expr) (from to : type) : Set := {}.

    (* When <<const>>ness changes in an initialization expression, it changes the
       <<const>>ness of the object that is being initialized. *)
    Axiom wp_init_cast_noop : forall ty e p Q,
        (let from := type_of e in
        match classify_cast from ty with
        | Some cst =>
            wp_init from p e (fun fr =>
              match cst with
              | AddConst ty => wp_make_const tu p ty (Q fr)
              | RemoveConst ty => wp_make_mutable tu p ty (Q fr)
              | Nothing => Q fr
              end)
        | None => UNSUPPORTED (unsupported_init_noop_cast e from ty)
        end)
      |-- wp_init ty p (Ecast (Cnoop ty) e) Q.
    Axiom wp_operand_cast_noop : forall ty e Q,
            wp_operand e (fun v free => has_type v ty ** Q v free)
        |-- wp_operand (Ecast (Cnoop ty) e) Q.

    Axiom wp_lval_cast_noop : forall ty e Q,
          (letI* p, free := wp_glval e in
           reference_to ty p ** Q p free)
      |-- wp_lval (Ecast (Cnoop $ Tref ty) e) Q.

    Axiom wp_xval_cast_noop : forall ty e Q,
          (letI* p, free := wp_glval e in
           reference_to ty p ** Q p free)
      |-- wp_xval (Ecast (Cnoop $ Trv_ref ty) e) Q.

    Definition int2bool_not_num (v : val) : Set.
    Proof. exact unit. Qed.

    Axiom wp_operand_cast_int2bool : forall e Q,
         (letI* v, free := wp_operand e in
          match v with
          | Vint n => Q (Vbool (bool_decide (n <> 0))) free
          | _ => ERROR (int2bool_not_num v)
          end)
      |-- wp_operand (Ecast Cint2bool e) Q.

    Definition ptr2bool_not_ptr (v : val) : Set.
    Proof. exact unit. Qed.

    Axiom wp_operand_cast_ptr2bool : forall e Q,
         (letI* v, free := wp_operand e in
          match v with
          | Vptr p => Q (Vbool (bool_decide (p <> nullptr))) free
          | _ => ERROR (ptr2bool_not_ptr v)
          end)
      |-- wp_operand (Ecast Cptr2bool e) Q.

    (** [Cfun2ptr] is a cast from a function to a pointer.

       Note that C and C++ classify function names differently:
       - in C, function names are Rvalues, and
       - in C++, function names are Lvalues

       We cannot write a rule for C functions without extending our
       treatment of value categories to account for this difference.
     *)
    Axiom wp_operand_cast_fun2ptr_cpp : forall e Q,
            wp_lval e (fun v => Q (Vptr v))
        |-- wp_operand (Ecast Cfun2ptr e) Q.

    (** [Cbuiltin2fun] is a cast from a builtin to a pointer.
     *)
    Axiom wp_operand_cast_builtin2fun_cpp : forall cc ar ret args g Q,
        let ty := Tfunction $ FunctionType (ft_cc:=cc) (ft_arity:=ar) ret args in
        let e := Eglobal g ty in
            wp_lval e (fun v => Q (Vptr v))
        |-- wp_operand (Ecast (Cbuiltin2fun $ Tptr ty) e) Q.

    (** Known places that bitcasts occur
        - casting between <<void*>> and <<T*>> for some <<T>>.
     *)
    Axiom wp_operand_cast_bitcast : forall e ty Q,
           (letI* v, free := wp_operand e in
             has_type v ty ** Q v free)
        |-- wp_operand (Ecast (Cbitcast ty) e) Q.

    (** [Cintegral] casts represent casts between integral types, e.g.
        - <<int>> -> <<short>>
        - <<short>> -> <<long>>
        - <<int>> -> <<unsigned int>>
        - <<enum Xxx>> -> <<int>>
     *)
    Axiom wp_operand_cast_integral : forall e t Q,
        wp_operand e (fun v free =>
           Exists v', [| conv_int tu (type_of e) t v v' |] ** Q v' free)
        |-- wp_operand (Ecast (Cintegral t) e) Q.

    Axiom wp_operand_cast_null : forall e ty Q,
        type_of e = Tnullptr ->
        is_pointer ty ->
            wp_operand e Q (* note: [has_type v Tnullptr |-- has_type v (Tptr ty)] *)
        |-- wp_operand (Ecast (Cnull2ptr ty) e) Q.

    Axiom wp_operand_cast_null2memberptr : forall cls e ty Q,
        type_of e = Tnullptr ->
            wp_operand e (fun _ free => Q (Vmember_ptr cls None) free)
        |-- wp_operand (Ecast (Cnull2memberptr $ Tmember_pointer (Tnamed cls) ty) e) Q.

    (* Determine if a 0-constant of this type can be used as a pseudonym for <<nullptr>> *)
    Definition can_represent_null (ty : type) : bool :=
      match ty with
      | Tnum _ _ => true
      | _ => false
      end.

    (* For backwards compatiblity, the C++ semantics allows treating 0-valued integer
       literals (of integral types) as synonymous with <<nullptr>>
       (cf. <https://en.cppreference.com/w/cpp/language/pointer#Null_pointers>).

       To make this rule compositional, we allow arbitrary integer expressions, but
       note that the front-end will only use this construct if the expression is
       exactly <<0>>.
     *)
    Axiom wp_operand_cast_null_int : forall e ty Q,
        can_represent_null (type_of e) ->
        is_pointer ty ->
            (letI* v, free := wp_operand e in
             [| v = Vint 0 |] ** Q (Vptr nullptr) free)
        |-- wp_operand (Ecast (Cnull2ptr ty) e) Q.

    (* note(gmm): in the clang AST, the subexpression is the call.
     * in essence, [Ecast Cuser] is a syntax annotation.
     *)
    Axiom wp_init_cast_user : forall e p ty Q,
        wp_init ty p e Q |-- wp_init ty p (Ecast Cuser e) Q.

    Axiom wp_operand_cast_user : forall e Q,
        wp_operand e Q |-- wp_operand (Ecast Cuser e) Q.

    (** [Cctor] casts are just syntactic sugar *)
    Axiom wp_operand_cast_ctor : forall t e Q,
        wp_operand e Q |-- wp_operand (Ecast (Cctor t) e) Q.

    (* TODO NAMES: does this need to check the types [t] and [t'] are
       consistent? *)
    Axiom wp_init_cast_ctor : forall p t' t e Q,
        wp_init t p e Q |-- wp_init t p (Ecast (Cctor t') e) Q.

    Definition UNSUPPORTED_reinterpret_cast (ty1 ty2 : type) : mpred.
    Proof. exact False%I. Qed.

    (*
    (** https://eel.is/c++draft/expr.reinterpret.cast

        NOTE there is a lot of subtlety around [reinterpret_cast]
     *)
    Axiom wp_operand_cast_reinterpret : forall e qt ty Q,
        match (* source *) type_of e , (* target *) qt with
        | Tptr _ , Tnum _ _ =>
          (* https://eel.is/c++draft/expr.reinterpret.cast#4
             A pointer can be explicitly converted to any integral type large
             enough to hold all values of its type. The mapping function is
             implementation-defined. *)
          wp_operand (Ecast (Cptr2int ty) e) Q
        | Tnum _ _ , Tptr _ =>
          (* A value of integral type or enumeration type can be explicitly
             converted to a pointer. A pointer converted to an integer of sufficient
             size (if any such exists on the implementation) and back to the same
             pointer type will have its original value; mappings between pointers
             and integers are otherwise implementation-defined. *)
          wp_operand (Ecast (Cint2ptr ty) e) Q
        | Tnullptr , Tnum _ _ =>
          (* A value of type [std​::​nullptr_t] can be converted to an integral type;
             the conversion has the same meaning and validity as a conversion of
             (void* )0 to the integral type.
           *)
          wp_operand e (fun _ free => Q (Vint 0) free)
        | Tptr (Tnum _ _), Tptr (Tnum W8 _) =>
          (* A narrow special case where the pointer does not change.
             This intentionally avoids the sources of struct pointers and union
             pointers because those might hit the "pointer-interconvertible"
             cases, where the pointer value might change.
           *)
            wp_operand e Q
        | ty1 , ty2 => UNSUPPORTED_reinterpret_cast ty1 ty2
        end
        |-- wp_operand (Ecast (Creinterpret qt) e) Q.
    *)

    (** Explicit casts are just sugar, the real cast is in the subexpression. *)
    Axiom wp_operand_explicit_cast : forall s t e Q,
          wp_operand e Q
      |-- wp_operand (Eexplicit_cast s t e) Q.

    Axiom wp_lval_explicit_cast : forall s t e Q,
          wp_lval e Q
      |-- wp_lval (Eexplicit_cast s t e) Q.

    Axiom wp_xval_explicit_cast : forall s t e Q,
          wp_xval e Q
      |-- wp_xval (Eexplicit_cast s t e) Q.

    (* TODO NAMES: does this need to check the types [t] and [t'] are
       consistent? *)
    Axiom wp_init_explicit_cast : forall p s t e Q,
          wp_init t p e Q
      |-- wp_init t p (Eexplicit_cast s t e) Q.

    (** You can cast anything to void, but an expression of type
        [void] can only be a pr_value *)
    Axiom wp_operand_cast_tovoid : forall e Q,
          wp_discard e (fun free => Q Vundef free)
      |-- wp_operand (Ecast C2void e) Q.

    Axiom wp_operand_cast_array2ptr : forall e Q,
        wp_glval e (fun p => Q (Vptr p))
        |-- wp_operand (Ecast Carray2ptr e) Q.

    (** [Cptr2int] exposes the pointer, which is expressed with [pinned_ptr]
     *)
    Axiom wp_operand_ptr2int : forall e ty Q,
        match drop_qualifiers (type_of e) , ty with
        | Tptr _ , Tnum sz sgn =>
          wp_operand e (fun v free => Exists p, [| v = Vptr p |] **
            (Forall va, pinned_ptr va p -* Q (Vint (match sgn with
                                                    | Signed => to_signed (int_rank.bitsize sz)
                                                    | Unsigned => trim (int_rank.bitsN sz)
                                                    end (Z.of_N va))) free))
        | _ , _ => False
        end
        |-- wp_operand (Ecast (Cptr2int ty) e) Q.

    (** [Cint2ptr] uses "angelic non-determinism" to allow the developer to
        pick any pointer that was previously exposed as the given integer.
     *)
    Axiom wp_operand_int2ptr : forall e ty Q,
        match unptr ty with
        | Some ptype =>
          wp_operand e (fun v free => Exists va : N, [| v = Vint (Z.of_N va) |] **
             (([| (0 < va)%N |] **
               Exists p : ptr,
                 pinned_ptr va p **
                 has_type (Vptr p) (Tptr ptype) **
                 Q (Vptr p) free) \\//
              ([| va = 0%N |] ** Q (Vptr nullptr) free)))
        | _ => False
        end
        |-- wp_operand (Ecast (Cint2ptr ty) e) Q.

    (** * [Cderived2base]
        casts from a derived class to a base class. Casting is only permitted
        on pointers and references
        - references occur with lvalues and xvalues
        - pointers occur with prvalues

        NOTE these casts require a side-condition that the [path] is valid
             in the program. We express this using the [valid_ptr] side
             condition, i.e. [valid_ptr addr] requires that [addr] only
             has valid paths.
             It would technically be a little nicer if this side condition
             was checked at "compile" time rather than at runtime.
     *)
    Axiom wp_lval_cast_derived2base : forall e ty path Q,
      match drop_qualifiers (type_of e), drop_qualifiers ty with
      | Tnamed derived , Tnamed base =>
          match derived_to_base_ty derived (path ++ [Tnamed base]) with
          | Some off =>
            wp_glval e (fun addr free =>
              let addr' := addr ,, off in
              reference_to ty addr' ** Q addr' free)
          | _ => False
          end
      | _, _ => False
      end
      |-- wp_lval (Ecast (Cderived2base path (Tref ty)) e) Q.

    Axiom wp_xval_cast_derived2base : forall e ty path Q,
      match drop_qualifiers (type_of e), drop_qualifiers ty with
      | Tnamed derived , Tnamed base =>
          match derived_to_base_ty derived (path ++ [Tnamed base]) with
          | Some off =>
              wp_glval e (fun addr free =>
                let addr' := addr ,, off in
                reference_to ty addr' ** Q addr' free)
          | _ => False
          end
      | _, _ => False
      end
      |-- wp_xval (Ecast (Cderived2base path (Trv_ref ty)) e) Q.

    Axiom wp_operand_cast_derived2base : forall e ty path Q,
      match drop_qualifiers <$> unptr (type_of e), drop_qualifiers ty with
      | Some (Tnamed derived) , Tnamed base =>
          match derived_to_base_ty derived (path ++ [Tnamed base]) with
          | Some off =>
            wp_operand e (fun addr free =>
              let addr' := _eqv addr ,, off in
              has_type (Vptr addr') (Tptr ty) ** Q (Vptr addr') free)
          | _ => False
          end
      | _, _ => False
      end
      |-- wp_operand (Ecast (Cderived2base path (Tptr ty)) e) Q.

    (* [Cbase2derived] casts from a base class to a derived class.
     *)
    Axiom wp_lval_cast_base2derived : forall e ty path Q,
      match drop_qualifiers (type_of e), drop_qualifiers ty with
      | Tnamed base , Tnamed derived =>
          match base_to_derived_ty derived (path ++ [Tnamed base]) with
          | Some off =>
            wp_glval e (fun addr free =>
              let addr' := addr ,, off in
              reference_to ty addr' ** Q addr' free)
          | _ => False
          end
      | _, _ => False
      end
      |-- wp_lval (Ecast (Cbase2derived path (Tref ty)) e) Q.

    Axiom wp_xval_cast_base2derived : forall e ty path Q,
      match drop_qualifiers (type_of e), drop_qualifiers ty with
      | Tnamed base , Tnamed derived =>
          match base_to_derived_ty derived (path ++ [Tnamed base]) with
          | Some off =>
              wp_glval e (fun addr free =>
                let addr' := addr ,, off in
                reference_to ty addr' ** Q addr' free)
          | _ => False
          end
      | _, _ => False
      end
      |-- wp_xval (Ecast (Cbase2derived path (Trv_ref ty)) e) Q.

    Axiom wp_operand_cast_base2derived : forall e ty path Q,
         match drop_qualifiers <$> unptr (type_of e), drop_qualifiers ty with
         | Some (Tnamed base), Tnamed derived =>
             match base_to_derived_ty derived (path ++ [Tnamed base]) with
             | Some off =>
                wp_operand e (fun addr free =>
                  let addr' := _eqv addr ,, off in
                  has_type (Vptr addr') (Tptr ty) ** Q (Vptr addr') free)
             | _ => False
             end
         | _, _ => False
        end
      |-- wp_operand (Ecast (Cbase2derived path (Tptr ty)) e) Q.

    (** the ternary operator [_ ? _ : _] has the value category
     * of the "then" and "else" expressions (which must be the same).
     * We express this with 4 rules, one for each of [wp_lval],
     * [wp_operand], [wp_xval], and [wp_init].
     *)
    Definition wp_cond {T} (wp : Expr -> (T -> FreeTemps.t -> epred) -> mpred) : Prop :=
      forall ty tst th el (Q : T -> FreeTemps -> mpred),
        Unfold WPE.wp_test (wp_test tst (fun c free =>
           if c
           then wp th (fun v free' => Q v (free' >*> free))
           else wp el (fun v free' => Q v (free' >*> free))))
        |-- wp (Eif tst th el ty) Q.

    Axiom wp_lval_condition : Reduce (wp_cond wp_lval).
    Axiom wp_xval_condition : Reduce (wp_cond wp_xval).
    Axiom wp_operand_condition : Reduce (wp_cond wp_operand).

    Axiom wp_init_condition : forall ty addr tst th el Q,
        Unfold WPE.wp_test (wp_test tst (fun c free =>
           if c
           then wp_init ty addr th (fun frees => Q (frees >*> free))
           else wp_init ty addr el (fun frees => Q (frees >*> free))))
        |-- wp_init ty addr (Eif tst th el ty) Q.

    Axiom wp_operand_implicit : forall e Q,
        wp_operand e Q |-- wp_operand (Eimplicit e) Q.
    Axiom wp_init_implicit : forall ty e p Q,
        wp_init ty p e Q |-- wp_init ty p (Eimplicit e) Q.

    (** Gets the type used in an expression like `sizeof` and `alignof` *)
    Definition get_type (ety : type + Expr) : type :=
      match ety with
      | inl ty => ty
      | inr e => type_of e
      end.

    (** `sizeof(ty)`
        https://eel.is/c++draft/expr.sizeof#1 and https://eel.is/c++draft/expr.sizeof#2
        When applied to a reference type, the size of the referenced type is used.

        While <<size_t>> is large enough to constrain the size in bytes of any object,
        <https://eel.is/c++draft/support.types#layout-3>

        > The type <<size_t>> is an implementation-defined unsigned integer type that
        > is large enough to contain the size in bytes of any object ([expr.sizeof]).

        dynamic expressions such as <<sizeof(int[n])>> for a variable <<n>> would allow
        constructing a value that violates this. Therefore, we require
        [has_type_prop sz Tsize_t].
     *)
    Axiom wp_operand_sizeof : forall ety ty Q,
        Exists sz,
          [| size_of (drop_reference $ get_type ety) = Some sz |] **
          [| has_type_prop sz Tsize_t |] **
          Q (Vn sz) FreeTemps.id
        |-- wp_operand (Esizeof ety ty) Q.

    (** `alignof(e)`
        https://eel.is/c++draft/expr.alignof

        NOTE: We do not require [has_type] in [wp_operand_alignof], this is guaranteed
        by the compiler.
     *)
    Axiom wp_operand_alignof : forall ety ty Q,
        Exists align,
          [| align_of (drop_reference $ get_type ety) = Some align |] **
          [| has_type_prop align Tsize_t |] **
          Q (Vn align) FreeTemps.id
        |-- wp_operand (Ealignof ety ty) Q.

    (** * Function calls

        The next few axioms rely on the evaluation order specified
        since C++17 (implemented in Clang >= 4):
        to evaluate [f(args)], [f] is evaluated before [args].

        Summary of the change: <https://stackoverflow.com/a/38798487/53974>.
        Official references (from <http://clang.llvm.org/cxx_status.html>):
        <http://www.open-std.org/jtc1/sc22/wg21/docs/papers/2016/p0400r0.html>
        <http://www.open-std.org/jtc1/sc22/wg21/docs/papers/2016/p0145r3.pdf>
     *)

    (** [wp_call ooe pfty f es Q] calls [f] taking the arguments from the
        evaluations of [es] and then acts like [Q].
        [pfty] is the type that the call is being carried out using,
        i.e. the syntactic type of the function (it is a pointer type).

        NOTE that the AST *must* insert implicit casts for casting
             qualifiers so that the types match up exactly up to top-level
             qualifiers, e.g. <<foo(const int)>> will be passed a value of
             type <<int>> (not <<const int>>). the issue with type-level
             qualifiers is addressed through the use of [normalize_type]
             below.
     *)
    Definition wp_call (ooe : evaluation_order.t) (pfty : type) (f : Expr) (es : list Expr)
      (Q : ptr -> FreeTemps -> epred) : mpred :=
      [| tu ⊧ resolve |] -*
      match unptr pfty with
      | Some fty =>
        let fty := normalize_type fty in
        match as_function fty with
        | Some targs =>
            let eval_f Q := wp_operand f (fun v fr => Exists fp, [| v = Vptr fp |] ** Q fp fr) in
            letI* fps, vs, ifree, free :=
               wp_args ooe [eval_f] (targs.(ft_params), targs.(ft_arity)) es in
            match fps with
            | [fp] => |> wp_fptr fty fp vs (fun v => interp ifree $ Q v free)
            | _ => UNREACHABLE ("wp_args did not return a singleton list for pre", fps)
            end
        | _ => False
        end
      | None => False
      end.

    Lemma wp_call_frame eo pfty f es Q Q' :
      Forall ps free, Q ps free -* Q' ps free |-- wp_call eo pfty f es Q -* wp_call eo pfty f es Q'.
    Proof.
      rewrite /wp_call.
      case_match; eauto.
      case_match; eauto.
      iIntros "K X Y".
      iSpecialize ("X" with "Y"); iRevert "X".
      iApply wp_args_frame.
      { simpl. iSplit; eauto.
        iIntros (??) "K". iApply wp_operand_frame. reflexivity.
        iIntros (??) "X". iDestruct "X" as (?) "[A B]".
        iExists _; iFrame "A". iApply "K"; eauto. }
      { iIntros (????).
        repeat case_match; eauto.
        iIntros "X"; iNext.
        iRevert "X". iApply wp_fptr_frame.
        iIntros (?). iApply interp_frame; iApply "K". }
    Qed.

    Axiom wp_lval_call : forall f (es : list Expr) Q (ty := type_of (Ecall f es)),
        wp_call (evaluation_order.order_of OOCall) (type_of f) f es (fun res free =>
           Reduce (lval_receive ty res $ fun v => Q v free))
        |-- wp_lval (Ecall f es) Q.

    Axiom wp_xval_call : forall f (es : list Expr) Q (ty := type_of (Ecall f es)),
        wp_call (evaluation_order.order_of OOCall) (type_of f) f es (fun res free =>
           Reduce (xval_receive ty res $ fun v => Q v free))
        |-- wp_xval (Ecall f es) Q.

    Axiom wp_operand_call : forall f es Q (ty := type_of (Ecall f es)),
        wp_call (evaluation_order.order_of OOCall) (type_of f) f es (fun res free =>
           operand_receive ty res $ fun v => Q v free)
       |-- wp_operand (Ecall f es) Q.

    Axiom wp_init_call : forall f es Q (addr : ptr) ty,
        (letI* res, free := wp_call (evaluation_order.order_of OOCall) (type_of f) f es in
             Reduce (init_receive addr res $ Q free))
      |-- wp_init ty addr (Ecall f es) Q.

    (** * Member calls *)

    (** [dispatch ct] performs dispatch on the function with the call type.

        Note that BRiCk considers [dispatch] to be something that occurs inside
        the "function" (i.e. after function entry <https://eel.is/c++draft/expr.call#note-7>).
        This aligns with the semantics of calling a [virtual] function through
        a member pointer, e.g. [(obj.*foo)(a,b,c)] when [foo] is a pointer to
        a [virtual] member function. The standard implementation of this pattern
        is to have the representation of member function pointers be closures
        that perform [virtual] resolution if necessary.
     *)
    Definition dispatch (ct : dispatch_type) (fty : functype) (fn : obj_name) (this_type : type)
      (obj : ptr) (args : list ptr) (Q : ptr -> epred) : mpred :=
      let fty := normalize_type fty in
      match ct with
      | Virtual =>
          match decompose_type this_type with
          | (tq, Tnamed cls) =>
              letI* fimpl_addr, impl_class, thisp := resolve_virtual obj cls fn in
              let this_type := tqualified tq (Tnamed impl_class) in
              |> wp_mfptr this_type fty fimpl_addr (thisp :: args) Q
          | _ => False
          end
      | Direct => |> wp_mfptr this_type fty (_global fn) (obj :: args) Q
      end.

    Lemma dispatch_frame ct fty fn this_type obj args Q Q' :
      (Forall p, Q p -* Q' p)
      |-- dispatch ct fty fn this_type obj args Q -*
          dispatch ct fty fn this_type obj args Q'.
    Proof.
      rewrite /dispatch.
      iIntros "Q".
      repeat case_match; try iIntros "[]".
      { iApply resolve_virtual_frame.
        iIntros (???). iIntros "X"; iNext; iRevert "X"; iApply wp_mfptr_frame. eauto. }
      { iIntros "X"; iNext; iRevert "X"; iApply wp_mfptr_frame. eauto. }
    Qed.

    (** [wp_mcall invoke ooe obj fty es Q] calls a member function on [obj].
        The function being called is embedded in the [invoke] function which
        handles the difference between virtual and direct dispatch.

        NOTE that the AST *must* insert implicit casts for casting qualifiers so
             that the types match up exactly up to top-level qualifiers, e.g.
             [foo(const int)] will be passed a value of type [int] (not [const
             int]). the issue with type-level qualifiers is addressed through
             the use of [normalize_type] below. *)

    Definition wp_mcall (arrow : bool) (invoke : ptr -> list ptr -> (ptr -> epred) -> mpred)
      ooe (obj : Expr) (fty : functype) (es : list Expr)
      (Q : ptr -> FreeTemps -> epred) : mpred :=
      [| tu ⊧ resolve |] -*
      let fty := normalize_type fty in
      match args_for <$> as_function fty with
      | Some targs =>
        letI* this, args, ifree, free := wp_args ooe [read_arrow arrow obj] targs es in
        match this with
        | [this] => invoke this args (fun v => interp ifree $ Q v free)
        | _ => False
        end
      | _ => False
      end.

    Lemma wp_mcall_frame arrow f this this_type fty es Q Q' :
      Forall p free, Q p free -* Q' p free
      |-- (Forall p ps Q Q', (Forall p, Q p -* Q' p) -* f p ps Q -* f p ps Q') -*
          wp_mcall arrow f this this_type fty es Q -* wp_mcall arrow f this this_type fty es Q'.
    Proof.
      rewrite /wp_mcall.
      case_match; eauto.
      iIntros "Q f X Y".
      iSpecialize ("X" with "Y"); iRevert "X".
      iApply wp_args_frame.
      { simpl. iSplitL; eauto. rewrite /wp.WPE.Mframe.
        iIntros (??) "X". iApply read_arrow_frame. eauto. }
      iIntros (????).
      case_match; try iIntros "[]".
      case_match; try iIntros "[]".
      iApply "f". iIntros (?); iApply interp_frame; iApply "Q".
    Qed.

    Axiom wp_lval_member_call : forall arrow ct fty f obj es vc cv nm Q,
        arrow_aggregate_type arrow (decltype_of_expr obj) = Some (vc, cv, nm) ->
        (let ty := type_of $ Emember_call arrow (inl (f, ct, fty)) obj es in
         let* res, free :=
           wp_mcall arrow (dispatch ct fty f $ tqualified cv (Tnamed nm)) (evaluation_order.order_of OOCall) obj fty es in
         lval_receive ty res $ fun v => Q v free)
        |-- wp_lval (Emember_call arrow (inl (f, ct, fty)) obj es) Q.

    Axiom wp_xval_member_call : forall arrow ct fty f obj es vc cv nm Q,
       arrow_aggregate_type arrow (decltype_of_expr obj) = Some (vc, cv, nm) ->
       (let ty := type_of $ Emember_call arrow (inl (f, ct, fty)) obj es in
        let* res, free :=
          wp_mcall arrow (dispatch ct fty f $ tqualified cv (Tnamed nm)) (evaluation_order.order_of OOCall) obj fty es in
        xval_receive ty res $ fun v => Q v free)
      |-- wp_xval (Emember_call arrow (inl (f, ct, fty)) obj es) Q.

    Axiom wp_operand_member_call : forall arrow ct fty f obj es vc cv nm Q,
        arrow_aggregate_type arrow (decltype_of_expr obj) = Some (vc, cv, nm) ->
        (let ty := type_of $ Emember_call arrow (inl (f, ct, fty)) obj es in
         let* res, free :=
           wp_mcall arrow (dispatch ct fty f $ tqualified cv (Tnamed nm)) (evaluation_order.order_of OOCall) obj fty es in
         operand_receive ty res $ fun v => Q v free)
      |-- wp_operand (Emember_call arrow (inl (f, ct, fty)) obj es) Q.

    Axiom wp_init_member_call : forall arrow ct f fty es (addr : ptr) vc cv nm obj ty Q,
        arrow_aggregate_type arrow (decltype_of_expr obj) = Some (vc, cv, nm) ->
        (let* res, free :=
           wp_mcall arrow (dispatch ct fty f $ tqualified cv (Tnamed nm)) (evaluation_order.order_of OOCall) obj fty es in
         init_receive addr res $ Q free)
     |-- wp_init ty addr (Emember_call arrow (inl (f, ct, fty)) obj es) Q.

    (** * Operator Calls
        These are calls (or member calls) that are written as operators
        and therefore have (potentially) different order-of-evaluation
        than regular function or member calls.
     *)
    Definition wp_operator_call oo oi es Q :=
      [| tu ⊧ resolve |] -*
      match oi with
      | operator_impl.Func f fty =>
          let fty := normalize_type fty in
          match args_for <$> as_function fty with
          | Some targs =>
            letI* fps, vs, ifree, free := wp_args (evaluation_order.order_of oo) [] targs es in
            |> wp_fptr fty (_global f) vs (fun v => interp ifree $ Q v free)
          | None => False
          end
       | operator_impl.MFunc fn ct fty =>
           match es with
           | eobj :: es =>
               wp_mcall false (dispatch ct fty fn (type_of eobj)) (evaluation_order.order_of oo) eobj fty es Q
           | _ => False
           end
      end%I.

    Lemma wp_operator_call_frame oo oi es Q Q' :
      (Forall p free, Q p free -* Q' p free) |-- wp_operator_call oo oi es Q -* wp_operator_call oo oi es Q'.
    Proof.
      rewrite /wp_operator_call.
      iIntros "F X Y".
      iSpecialize ("X" with "Y"); iRevert "X".
      repeat case_match; try solve [ iIntros "[]" ].
      { iApply wp_args_frame; eauto.
        iIntros (????) "W !>"; iRevert "W";
          iApply wp_fptr_frame; iIntros (?); iApply interp_frame.
        iApply "F". }
      { iApply (wp_mcall_frame with "F").
        iIntros (????) "F".
        by iApply dispatch_frame. }
    Qed.

    Axiom wp_operand_operator_call : forall oo oi es (ty := type_of $ Eoperator_call oo oi es) Q,
        (letI* res, free := wp_operator_call oo oi es in
         operand_receive ty res $ fun v => Q v free)
     |-- wp_operand (Eoperator_call oo oi es) Q.
    Axiom wp_lval_operator_call : forall oo oi es (ty := type_of $ Eoperator_call oo oi es) Q,
        (letI* res, free := wp_operator_call oo oi es in
         lval_receive ty res $ fun v => Q v free)
     |-- wp_lval (Eoperator_call oo oi es) Q.
    Axiom wp_xval_operator_call : forall oo oi es (ty := type_of $ Eoperator_call oo oi es) Q,
        (letI* res, free := wp_operator_call oo oi es in
         xval_receive ty res $ fun v => Q v free)
     |-- wp_xval (Eoperator_call oo oi es) Q.
    Axiom wp_init_operator_call : forall addr oo oi es (ty := type_of $ Eoperator_call oo oi es) Q,
        (letI* res, free := wp_operator_call oo oi es in
         init_receive addr res $ Q free)
     |-- wp_init ty addr (Eoperator_call oo oi es) Q.

    (* null *)
    Axiom wp_null : forall Q,
      Q (Vptr nullptr) FreeTemps.id
      |-- wp_operand Enull Q.

    (** The lifetime of an object can be ended at an arbitrary point
        without calling the destructor
        (<http://eel.is/c++draft/basic.life#5>). According to
        <http://eel.is/c++draft/basic.life#5>, a program has UB if it
        depends on the side effects of the destructor if it is not
        explicitly called before the storage is reused. This is
        reflected here by not doing the ownership manipulation that
        the destructor would potentially do. *)
    Axiom end_provides_storage : forall storage_ptr obj_ptr aty sz,
       size_of aty = Some sz ->
       provides_storage storage_ptr obj_ptr aty ** obj_ptr |-> anyR aty 1$m
       |-- |={⊤}=> (storage_ptr |-> blockR sz 1$m).

    (** temporary expressions
       note(gmm): these axioms should be reviewed thoroughly
     *)
    (* Clang's documentation for [ExprWithCleanups] states:

       > Represents an expression – generally a full-expression – that
       > introduces cleanups to be run at the end of the sub-expression's
       > evaluation.

       Therefore, we destroy temporaries created when evaluating [e]
       before running the continuation.

       NOTE: We follow C++'s AST rules for destroying temporaries appropriately
       so these nodes should effectively be no-ops, though there are certain
       places in the AST that has odd evaluation semantics
     *)
    Axiom wp_lval_clean : forall e Q,
          wp_lval e (fun p frees => interp frees $ Q p FreeTemps.id)
      |-- wp_lval (Eandclean e) Q.
    Axiom wp_xval_clean : forall e Q,
          wp_xval e (fun p frees => interp frees $ Q p FreeTemps.id)
      |-- wp_xval (Eandclean e) Q.
    Axiom wp_operand_clean : forall e Q,
          wp_operand e (fun v frees => interp frees $ Q v FreeTemps.id)
      |-- wp_operand (Eandclean e) Q.
    Axiom wp_init_clean : forall ty e addr Q,
          wp_init ty addr e (fun frees => interp frees $ Q FreeTemps.id)
      |-- wp_init ty addr (Eandclean e) Q.

    (** [Ematerialize_temp e ty] is an xvalue that gets memory (with automatic
        storage duration) and initializes it using the expression.
     *)
    Axiom wp_xval_temp : forall e Q,
        (let ty := type_of e in
         Forall a : ptr,
         wp_initialize ty a e (fun frees => Q a (FreeTemps.delete ty a >*> frees)))
        |-- wp_xval (Ematerialize_temp e Xvalue) Q.

    Axiom wp_lval_temp : forall e Q,
        (let ty := type_of e in
         Forall a : ptr,
         wp_initialize ty a e (fun frees => Q a (FreeTemps.delete ty a >*> frees)))
        |-- wp_lval (Ematerialize_temp e Lvalue) Q.

    (** Pseudo destructors arise from calling the destructor on
        an object of templated type when the type is instantiated
        with a primitive. For example,

        <<
          template<typename T> void destroy_it(T* t) { t->~T(); }
        >>

        with [T = int].

        To maintain similarity with the rest of the system,
        the C++ abstract machine "implements" this with what is (essentially)
        a function with the specification:

        [[
           \pre this |-> anyR ty 1
           \post this |-> tblockR ty
        ]]

        Note that the memory is *not* returned to the C++ abstract
        machine because this is not reclaimation for an object going
        out of scope.

        TODO(gmm): These two rules are conservative.
        - They requires a mutable object which means that it can not be used
          to destroy <const> objects.
     *)
    Axiom wp_operand_pseudo_destructor : forall e ty Q,
        (letI* v, free := wp_glval e in
         v |-> anyR ty 1$m ** (v |-> tblockR ty 1$m -* Q Vvoid free))
        |-- wp_operand (Epseudo_destructor false ty e) Q.
    Axiom wp_operand_pseudo_destructor_arrow : forall e ty ety (_ : (unptr $ type_of e) = Some ety) Q,
        (letI* v, free := wp_glval (Ederef e ety) in
         v |-> anyR ty 1$m ** (v |-> tblockR ty 1$m -* Q Vvoid free))
        |-- wp_operand (Epseudo_destructor true ty e) Q.

    (* [Eimplicit_init] nodes reflect implicit /value initializations/ which are inserted
       into the AST by Clang [1]. The C++ standard states that value initializations [2]
       are equivalent to zero initializations for non-class and non-array types [3];
       zero initializations are documented here [4].

       [1] https://clang.llvm.org/doxygen/classclang_1_1ImplicitValueInitExpr.html#details
       [2] https://eel.is/c++draft/dcl.init#general-8
       [3] https://eel.is/c++draft/dcl.init#general-8.3
       [4] https://eel.is/c++draft/dcl.init#general-6
     *)

    Definition zero_init_val (ty : type) : option val :=
      match representation_type tu ty with
      | Tnullptr | Tptr _  => Some $ Vptr nullptr
      (* | Tmember_pointer _ _ *)
      | Tchar_ _ => Some $ Vchar 0
      | Tbool => Some $ Vbool false
      | Tnum _ _ => Some $ Vint 0
      | _ => None
      end.

    Lemma zero_init_val_is_scalar ty v : zero_init_val ty = Some v -> is_scalar_type ty = true.
    Proof.
      rewrite /zero_init_val/is_scalar_type/representation_type /=. destruct (drop_qualifiers ty) eqn:Hdrop => //; eauto.
    Qed.

    Lemma well_typed_zero_init_val (MOD : tu ⊧ resolve) : forall ty v,
        zero_init_val ty = Some v -> has_type_prop v ty.
    Proof.
      rewrite /zero_init_val/representation_type. intros.
      eapply has_type_prop_drop_qualifiers; revert H.
      destruct (drop_qualifiers ty) eqn:Heq; simpl; try inversion 1; subst.
      - apply has_nullptr_type.
      - apply has_int_type. rewrite /bitsize.bound.
        destruct sz, sgn; compute; intuition congruence.
      - apply has_type_prop_char_0.
      - eapply has_type_prop_enum.
        clear H1. revert H.
        rewrite /underlying_type/=.
        destruct (tu.(types) !! gn) eqn:Hglobal => /= //; rewrite Hglobal /= //.
        destruct g => /=//.
        intros. do 3 eexists; split; eauto; split; eauto.
        case_match; try congruence; inversion H; subst; simpl; split; try tauto.
        + apply has_nullptr_type.
        + apply has_int_type. rewrite /bitsize.bound; destruct sz,sgn; compute; intuition congruence.
        + apply has_type_prop_char_0.
        + apply has_type_prop_bool; eauto.
        + eapply has_type_prop_nullptr; eauto.
      - apply has_type_prop_bool. eauto.
      - eapply has_type_prop_nullptr; eauto.
    Qed.

    Lemma zero_init_val_erase_drop ty :
      zero_init_val (erase_qualifiers ty) = zero_init_val (drop_qualifiers ty).
    Proof. by induction ty. Qed.

    Axiom wp_operand_implicit_init : forall ty v Q,
          zero_init_val ty = Some v ->
          Q v FreeTemps.id
      |-- wp_operand (Eimplicit_init ty) Q.

    Definition marg_types (t : functype) : option (list type * function_arity) :=
      match t with
      | Tfunction {| ft_cc:=cc ; ft_arity:=ar ; ft_params := _ :: args |} =>
          (* we drop the first argument which is for [this] *)
          Some (args, ar)
      | _ => None
      end.

    Definition type_of_ctor tu obj : option type :=
      match tu.(symbols) !! obj with
      | Some (Oconstructor ctor as v) => Some (type_of_value v)
      | _ => None
      end.

    Axiom wp_init_constructor : forall cls ty cv (this : ptr) cnd es Q,
      decompose_type ty = (cv, Tnamed cls) ->
        (* NOTE because the AST does not include the types of the arguments of
           the constructor, we have to look up the type in the environment.
         *)
           match type_of_ctor tu cnd with
           | Some ctor_type =>
             match marg_types ctor_type with
             | Some arg_types =>
                letI* _, argps, ifree, free := wp_args evaluation_order.nd nil arg_types es in
                |> (this |-> tblockR (Tnamed cls) 1$m -*
                   (* ^^ The semantics currently has constructors take ownership of a [tblockR] *)
                   letI* resultp := wp_fptr ctor_type (_global cnd) (this :: argps) in
                   letI* := interp ifree in
                    (* in the semantics, constructors return [void] *)
                    resultp |-> primR Tvoid 1$m Vvoid **
                    let Q := Q free in
                    if q_const cv
                    then wp_make_const tu this (Tnamed cls) Q
                    else Q)
             | _ => False (* unreachable b/c we got a constructor *)
             end
           | _ => ERROR ("Constructor not found.", cnd)
           end
      |-- wp_init ty this (Econstructor cnd es ty) Q.

    Axiom wp_init_lambda : forall ty cls (this : ptr) es Q,
          wp_init ty this (Einitlist es None (Tnamed cls)) Q
      |-- wp_init ty this (Elambda cls es) Q.

    Fixpoint wp_array_init (ety : type) (base : ptr) (es : list Expr) (idx : Z)
      (Q : FreeTemps -> mpred) : mpred :=
      match es with
      | nil =>
        Q FreeTemps.id
      | e :: rest =>
          (* NOTE: We nest the recursive calls to `wp_array_init` within
               the continuation of the `wp_initialize` statement to
               reflect the fact that the C++ Standard introduces
               sequence-points between all of the elements of an
               initializer list (c.f. http://eel.is/c++draft/dcl.init.list#4)
           *)
         letI* free := wp_initialize ety (base .[ erase_qualifiers ety ! idx ]) e in
         interp free $ wp_array_init ety base rest (Z.succ idx) Q
      end.

    Lemma wp_array_init_frame ety base : forall es ix Q Q',
      (Forall f, Q f -* Q' f)
      |-- wp_array_init ety base es ix Q -*
          wp_array_init ety base es ix Q'.
    Proof.
      induction es; simpl; intros; iIntros "X".
      { iIntros "A"; iApply "X"; iApply "A"; done. }
      { iApply wp_initialize_frame; [done|]. iIntros (?).
        iApply interp_frame. by iApply IHes. }
    Qed.

    Definition fill_initlist (desiredsz : N) (es : list Expr) (f : Expr) : list Expr :=
      let actualsz := N.of_nat (length es) in
      es ++ replicateN (desiredsz - actualsz) f.

    (** NOTE this assumes that the C++ abstract machine already owns the array
        that is being initialized, see [wp_init_initlist_array] *)
    Definition wp_array_init_fill (ety : type) (base : ptr) (es : list Expr) (f : option Expr) (sz : N)
               (Q : FreeTemps -> mpred) : mpred :=
      let len := N.of_nat (length es) in
      let Q free :=
          base |-> type_ptrR (Tarray (erase_qualifiers ety) sz) -* Q free
      in
      match (len ?= sz)%N with
      | Lt =>
          match f with
          | None => False
          | Some fill => wp_array_init ety base (fill_initlist sz es fill) 0 Q
          end
      | Eq => wp_array_init ety base es 0 Q
      (* <http://eel.is/c++draft/dcl.init.general#16.5>

         Programs which contain more initializer expressions than
         array-members are ill-formed.
       *)
      | Gt => False
      end.

    Lemma wp_array_init_fill_frame ety base es f sz Q Q' :
      (Forall f, Q f -* Q' f)
      |-- wp_array_init_fill ety base es f sz Q -*
          wp_array_init_fill ety base es f sz Q'.
    Proof.
      rewrite /wp_array_init_fill.
      case_match; eauto.
      { iIntros "H"; iApply wp_array_init_frame.
        iIntros (?) "A B"; iApply "H"; iApply "A"; done. }
      { case_match; eauto.
        iIntros "H".
        iApply wp_array_init_frame.
        iIntros (?) "A B"; iApply "H"; iApply "A"; done. }
    Qed.

    (** [is_array_of aty ety] checks that [aty] is a type representing an
        array of [ety].
     *)
    Definition is_array_of (aty ety : type) : Prop :=
      match aty with
      | Tincomplete_array ety' => ety = ety'
      | Tvariable_array ety' _ => ety = ety'
      | Tarray ety' _ => ety = ety'
      | _ => False
      end.

    (** Initializing an array using an initializer list.
        In the clang AST, the types [ty] and [Tarray ety sz] are now always the
        same, in particular, in the expression `new C[10]{}`. We say that
        the index to [wp_init] is the dynamic type and [type_of (Einitlist ..)]
        is the static type. For santity, we require that the general shape of the
        two types match, but we pull the size of the array from the dynamic type.
     *)
    Axiom wp_init_initlist_array : forall ls fill ty ety (sz : N) (base : ptr) Q, (* sz' <= sz *)
          is_array_of ty ety ->
          wp_array_init_fill ety base ls fill sz Q
      |-- wp_init (Tarray ety sz) base (Einitlist ls fill ty) Q.


    (* https://eel.is/c++draft/dcl.init#general-7.2 says that "To
    default-initialize an object of type T means: If T is an array type, each
    element is default-initialized." Clang emits [Econstructor ... (Tarray
    (Tnamed ...))] initializing expressions for those cases, where the
    Econstructor node indicates the constructor for the *elements* in the
    array.

    We assume that the elements of the array are initialized from
    left to right, i.e. from the first element to the last element. The
    standard is not explicit about the initialization order for default
    initialization of arrays, but the standard does explicitly specify this
    ordering for arrays with an explicit element list
    <https://eel.is/c++draft/dcl.init#general-15.5>. The standard also demands
    destructors to be run in opposite order <https://eel.is/c++draft/dcl.init.general#19>,
    and it's expected that every object "is destroyed in the exact reverse order
    it was constructed." (<https://doi.org/10.1145/2103656.2103718>,
    <https://eel.is/c++draft/expr.delete#6>). Therefore, it seems
    reasonable to assume that the same ordering applies for default
    initialization. For this reason, the rule for default initalization
    simply defers to the rule for initialization with an empty initializer
    list. *)
    Axiom wp_init_default_array : forall ty ety sz base ctorname args Q,
          is_array_of ty ety ->
          wp_array_init_fill ety base [] (Some $ Econstructor ctorname args ety) sz Q
      |-- wp_init (Tarray ety sz) base (Econstructor ctorname args ty) Q.

    Axiom wp_operand_initlist_default : forall t Q,
          match get_default t with
          | None => False
          | Some v => Q v FreeTemps.id
          end
      |-- wp_operand (Einitlist nil None t) Q.

    Axiom wp_operand_initlist_prim : forall t e Q,
          (if prim_initializable t
           then wp_operand e Q
           else False)
      |-- wp_operand (Einitlist (e :: nil) None t) Q.

    Definition struct_inits (s : Struct) (es : list Expr) : option (list Initializer) :=
      let info :=
          map (fun b e => {| init_path := InitBase b.1
                        ; init_init := e |}) s.(s_bases) ++
          map (fun m e => {| init_path := InitField m.(mem_name)
                        ; init_init := e |}) s.(s_fields)
      in
      if bool_decide (length info = length es) then
        Some $ List.map (fun '(f,e) => f e) $ combine info es
      else None.

    Fixpoint wp_each (ps : list (ptr * type * Expr)) (free : FreeTemps.t)(Q : FreeTemps.t -> epred) : mpred :=
      match ps with
      | nil => Q free
      | (p, t, e) :: ps =>
          let* free' := wp_initialize t p e in
          wp_each ps (free' >*> free) Q
      end.

    Definition wp_struct_initlist (cls : globname) (s : Struct) (es : list Expr) (this : ptr)
      (Q : FreeTemps.t -> epred) : mpred :=
      (if bool_decide (length es = length s.(s_bases) + length s.(s_fields)) then
         let* free :=
           wp_each ((fun '(b, e) => (this ,, _base cls b.1, Tnamed b.1, e)) <$> combine s.(s_bases) es) FreeTemps.id in
         let* := wp_init_identity this tu cls in
         let* free :=
           wp_each ((fun '(m, e) => (this ., (Field cls m.(mem_name)), m.(mem_type), e)) <$> (combine s.(s_fields) $ skipn (length s.(s_bases)) es)) free in
         this |-> structR cls 1$m -* Q free
       else False)%I.


    (* The standard allows initializing unions in a variety of ways.
       See <https://eel.is/c++draft/dcl.init.aggr#5>. However, the cpp2v
       frontend desugars all of these to initialize exactly one element.
     *)
    Fixpoint find_member (fld : field_name.t) (ls : list Member) {struct ls} : option (nat * Member) :=
      match ls with
      | nil => None
      | m :: ms =>
          if bool_decide (m.(mem_name) = fld) then
            Some (0, m)
          else
            first S <$> find_member fld ms
      end.

    Definition wp_union_initlist (cls : globname) (u : decl.Union)
      (fld : field_name.t) (e : option Expr) (this : ptr)
      (Q : FreeTemps.t -> epred) : mpred :=
      match find_member fld u.(u_fields) with
      | None => False (* UNSUPPORTED *)
      | Some (n, m) =>
          let field_ptr : ptr := this ., (Field cls fld) in
          letI* free :=
            match e with
            | Some init => wp_initialize m.(mem_type) field_ptr init
            | None => default_initialize tu m.(mem_type) field_ptr
            end
          in
          this |-> unionR cls 1$m (Some n) -* Q free
      end%I.

    (** Using an initializer list to create a `struct`.

       NOTE clang elaborates the initializer list to directly match the members
       of the target class. For example, consider `struct C { int x; int y{3}; };`
       1. `{0}` is elaborated into `{0, 3}`;
       2. `{.y = 7, .x = 2}` is elaborated into `{2, 7}`

       Base classes are also elements. See https://eel.is/c++draft/dcl.init.aggr#2.2

       Note: the C++ standard text provides a special caveat for members
       of anonymous unions, but cpp2v represents anonymous unions as regular
       named unions and the front-end desugars initializer lists accordingly.
     *)
    Axiom wp_init_initlist_struct : forall cls (base : ptr) cv es ty Q,
        decompose_type ty = (cv, Tnamed cls) ->
        (let do_const Q :=
           if q_const cv
           then wp_make_const tu base (Tnamed cls) Q
           else Q
         in
         match tu.(types) !! cls with
         | Some (Gstruct s) =>
             letI* free := wp_struct_initlist cls s es base in
             do_const (Q free)
         | _ => False
         end)
      |-- wp_init ty base (Einitlist es None ty) Q.

    Axiom wp_init_initlist_union : forall cls (base : ptr) fld cv e ty Q,
        decompose_type ty = (cv, Tnamed cls) ->
        (let do_const Q :=
           if q_const cv
           then wp_make_const tu base (Tnamed cls) Q
           else Q
         in
         match tu.(types) !! cls with
         | Some (Gunion u) =>
             letI* free := wp_union_initlist cls u fld e base in
             do_const (Q free)
         | _ => False
         end)
      |-- wp_init ty base (Einitlist_union fld e ty) Q.

  End with_resolve.

  (* `Earrayloop_init` needs to extend the region, so we need to start a new section. *)
  Section with_resolve__arrayloop.
    Context `{Σ : cpp_logic} {σ : genv}.
    Variable (tu : translation_unit).

    #[local] Notation interp := (interp tu).

    (* `Earrayloop_init` and `Earrayloop_index` correspond, respectively,
       to the `ArrayInitLoopExpr`[1] and `ArrayInitIndexExpr`[2] expressions
       from clang. While these expressions are not a part of the C++ standard,
       we can still ascribe a useful semantics.

       In particular, this is a restricted loop so we ascribe the semantics by
       unrolling. On each iteration, the C++ Abstract Machine binds a distinguished
       variable ("!loop_index", which is not a valid identifier in C++) so that
       `Earrayloop_index` can read the value. We semantically treat this variable
       as a constant, so we only give `1/2` fraction to it and demand it back at the
       end of each iteration, preferring to do the incrementing in the logic rather
       than using the program syntax.

       For example, the following `Earrayloop_init` expression has the same
       semantics as the C++ loop which follows it /except/ that the array
       we are initializing is only evaluated once (c.f. [1]):
       ```
       (* Coq *)
       Earrayloop_init 16 target init (Tarray ``::uint8`` 16)

       (* C++ *)
       for (int "!loop_index" = 0; "!loop_index" < 16; "!loop_index"++) {
           target["!loop_index"] = init;
       }
       ```

       [1] https://clang.llvm.org/doxygen/classclang_1_1ArrayInitLoopExpr.html#details
       [2] https://clang.llvm.org/doxygen/classclang_1_1ArrayInitIndexExpr.html#details
     *)

    (* Maybe we can `Rbind (opaque n) p`, and then add `_opaque` to encapsulate looking this up in the region;
       the new premise would be (after Loc:=ptr goes in) `Q _opaque` *)

    Axiom wp_lval_opaque_ref : forall n ρ ty Q,
          wp_lval tu ρ (Evar (localname.opaque n) ty) Q
      |-- wp_lval tu ρ (Eopaque_ref n (Tref ty)) Q.

    Axiom wp_xval_opaque_ref : forall n ρ ty Q,
          wp_lval tu ρ (Evar (localname.opaque n) ty) Q
      |-- wp_xval tu ρ (Eopaque_ref n (Trv_ref ty)) Q.

    (* Maybe do something similar to what was suggested for `wp_lval_opaque_ref` above. *)
    Axiom wp_operand_arrayloop_index : forall ρ level ty Q,
          Exists v,
            ((Exists q, _local ρ (localname.arrayloop_index level)
                               |-> primR (erase_qualifiers ty) q v) **
              True) //\\ Q v FreeTemps.id
      |-- wp_operand tu ρ (Earrayloop_index level ty) Q.

    (* The following loop is essentially the following:
       recursion of `sz`:
       ```
       Fixpoint _arrayloop_init
                (ρ : region) (level : N)
                (targetp : ptr) (init : Expr)
                (ty : type) (Q : FreeTemps -> epred)
                (sz : nat) (idx : N)
                {struct sz}
         : mpred :=
         let loop_index := _local ρ (loop_index level) in
         match sz with
         | O => Q emp
         | S sz' =>
           _at loop_index (primR Tsize_t (1/2) idx) -*
           wp_init ρ ty (Vptr $ _offset_ptr targetp $ o_sub resolve ty idx) init
                   (fun free => free **
                      _at loop_index (primR Tulonglong (1/2) idx) **
                      _arrayloop_init level sz' ρ (S idx) targetp init ty Q)
         end%I.
       ```

       We use `N.peano_rect` to avoid potentially building a large natural number.
     *)
    Definition _arrayloop_init
               (ρ : region) (level : N)
               (targetp : ptr) (init : Expr)
               (ty : type) (Q : epred)
               (* The arguments above this comment are constant throughout the recursion.

                  The arguments below this line will change during the recursion.
                *)
               (sz : N) (idx : N)
      : mpred :=
      let loop_index := _local ρ (localname.arrayloop_index level) in
      N.peano_rect (fun _ : N => N -> mpred)
                   (fun _ => Q)
                   (fun _ rest idx =>
                      (* NOTE The abstract machine only provides 1/2 of the ownership
                           to the program to make it read-only.
                         NOTE that no "correct" program will ever modify this variable
                           anyways. *)
                      loop_index |-> primR Tsize_t 1$c idx -*
                      wp_initialize tu ρ ty (targetp .[ erase_qualifiers ty ! idx ]) init
                              (fun free => interp free $
                                 loop_index |-> primR Tsize_t 1$c idx **
                                 rest (N.succ idx))) sz idx.

    Axiom wp_init_arrayloop_init : forall oname level sz ρ (trg : ptr) src init ety ty Q,
          has_type_prop (Vn sz) Tsize_t ->
          is_array_of ty ety ->
          wp_glval tu ρ src
                   (fun p free =>
                      Forall idxp,
                      trg |-> validR -*
                      _arrayloop_init (Rbind (localname.opaque oname) p
                                             (Rbind (localname.arrayloop_index level) idxp ρ))
                                      level trg init ety
                                      (trg |-> type_ptrR (Tarray ety sz) -* Q free)
                                      sz 0)
      |-- wp_init tu ρ (Tarray ety sz) trg
                    (Earrayloop_init oname src level sz init ty) Q.

    (* This is here, rather than being next to [Eif] because the evaluation
       requires extending the region (for the temporary)
       NOTE that the clang documentation states that the 'else' branch is defined in
       terms of the opaque value, but, it does not seem possible for the opaque value to
       be used in this expression.
     *)
    Definition wp_cond2 {T} (wp : translation_unit -> region -> Expr -> (T -> FreeTemps.t -> epred) -> mpred) : Prop :=
      forall tu ρ n ty common tst th el (Q : T -> FreeTemps -> mpred),
        Forall p,
           wp_initialize tu ρ (type_of common) p common (fun free =>
           let ρ' := Rbind (localname.anon n) p ρ in
           wp_test tu ρ' tst (fun c free'' =>
             let free := (free'' >*> FreeTemps.delete ty p >*> free)%free in
             if c
             then wp tu ρ' th (fun v free' => Q v (free' >*> free))
             else wp tu ρ' el (fun v free' => Q v (free' >*> free))))
        |-- wp tu ρ (Eif2 n common tst th el ty) Q.

    Axiom wp_lval_condition2 : Reduce (wp_cond2 wp_lval).
    Axiom wp_xval_condition2 : Reduce (wp_cond2 wp_xval).
    Axiom wp_operand_condition2 : Reduce (wp_cond2 wp_operand).

    (* Note: This one is more subtle because the [free] from the [wp_initialize]
       could (in theory) be the [free] for the then branch. This happens if the
       [then] branch is just a reference to the opaque value.
       This would only be possible if, for example,
       ```
       C x = C(1) ?: C();
       ```
       could be compiled *without* materializing a temporary. This would require:
       1. constructing `C(1)` into the memory for `x`
       2. if `(bool)(C(1))` is false, then calling (effectively) `x.~C()` and then
          constructing `C()` into `x`.
       Generally, this violates the rule that temporaries are destroyed at the
       end of the full expression because (in this trace), `C(1)` would be
       constructing a temporary.
     *)
    Axiom wp_init_condition2 : forall tu ρ n ty common tst th el p Q,
        Forall p,
           wp_initialize tu ρ (type_of common) p common (fun free =>
           let ρ' := Rbind (localname.opaque n) p ρ in
           wp_test tu ρ' tst (fun c free'' =>
             let free := (free'' >*> FreeTemps.delete ty p >*> free)%free in
             if c
             then wp_init tu ρ' ty p th (fun free' => Q (free' >*> free))
             else wp_init tu ρ' ty p el (fun free' => Q (free' >*> free))))
        |-- wp_init tu ρ ty p (Eif2 n common tst th el ty) Q.

  End with_resolve__arrayloop.
End Expr.

Declare Module E : Expr.

Export E.

Export cfrac.
