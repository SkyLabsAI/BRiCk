(*
 * Copyright (c) 2020-2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.iris.extra.proofmode.proofmode.
Require Import bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.semantics.
Require Import bluerock.lang.cpp.logic.pred.
Require Import bluerock.lang.cpp.logic.path_pred.
Require Import bluerock.lang.cpp.logic.heap_pred.
Require Import bluerock.lang.cpp.logic.wp.
Require Import bluerock.lang.cpp.logic.initializers.
Require Import bluerock.prelude.letstar.

(* BEGIN UPSTREAM *)
Lemma big_opL_map {PROP : bi} : forall {T U} (g : U -> T) ps (f : nat -> T -> PROP),
    big_opL bi_sep f (map g ps) -|- big_opL bi_sep (fun a b => f a (g b)) ps.
Proof.
  induction ps; simpl; intros.
  - reflexivity.
  - rewrite IHps. reflexivity.
Qed.

Lemma big_opL_all  {PROP : bi} (T : Type) (P : T -> PROP) (ls : list T) :
  bi_intuitionistically (Forall x, P x) |-- [∗list] x ∈ ls , P x.
Proof.
  induction ls; simpl; eauto.
  iIntros "#H". iSplitL.
  iApply "H". iApply IHls. iApply "H".
Qed.
(* END UPSTREAM *)

Fixpoint split_at {T : Type} (n : nat) (ls : list T) : list T * list T :=
  match n , ls with
  | 0 , _ => (nil, ls)
  | S n , [] => (nil, nil)
  | S n , l :: ls => let '(a,b) := split_at n ls in (l :: a, b)
  end.

Lemma split_at_firstn_skipn {T} (ls : list T) : forall (n : nat),
    split_at n ls = (firstn n ls, skipn n ls).
Proof.
  induction ls; destruct n; simpl; eauto.
  rewrite IHls; done.
Qed.

Definition check_arity (ts : list decltype) (ar : function_arity) (es : list Expr) : bool :=
  match Nat.compare (length ts) (length es) with
  | Eq => true
  | Lt => bool_decide (ar = Ar_Variadic)
  | Gt => false
  end.

Definition setup_args (ts : list decltype) (ar : function_arity) (es : list Expr)
    : (list (decltype * Expr) * option nat) :=
  let normal_params := length ts in
  let (regular, variadic) := split_at normal_params es in
  (combine ts regular ++ map (fun e => (type_of e, e)) variadic,
    match ar with
    | Ar_Definite => None
    | Ar_Variadic => Some normal_params
    end).

(**
  BEGIN destruction-of-function-arguments
  Destruction of function arguments is left implementation defined
  in C++. See <https://eel.is/c++draft/expr.call#6> which states:

  > It is implementation-defined whether the lifetime of a parameter
  > ends when the function in which it is defined returns or at the
  > end of the enclosing full-expression. The initialization and
  > destruction of each parameter occurs within the context of the
  > calling function.

  In the BRiCk semantics, we follow the Itanium ABI which destroys
  trivially destructible objects immediately and otherwise destroys
  objects at the end of the full expression. See
  <https://refspecs.linuxbase.org/cxxabi-1.83.html#call>.
  END destruction-of-function-arguments
 *)

Section with_resolve.
  Context `{Σ : cpp_logic} {σ : genv} (tu : translation_unit).
  Variables (ρ : region).
  Implicit Types (p : ptr).

  (* [wp_arg ty e K] evaluates [e] to initialize a parameter of type [ty].

     This function does *not* add temporary destruction for trivially
     destructible types so that they can be destroyed eagerly.

     NOTE: This means that the order of construction and destruction of
           these trivial objects will not follow the stack discipline,
           but since these destructors are trivial, the difference is
           not observable.
   *)
  #[local]
  Definition wp_arg (ty : decltype) e K :=
    Forall p,
      letI* free := wp_initialize tu ρ ty p e in
      K p (if is_trivially_destructible tu ty
           then free
           else FreeTemps.delete ty p >*> free)%free.
  #[global] Arguments wp_arg _ _ _ /.

  Lemma wp_arg_frame : forall ty e, |-- wp.WPE.Mframe (wp_arg ty e) (wp_arg ty e).
  Proof.
    rewrite /wp.WPE.Mframe; intros.
    iIntros (??) "X Y %p".
    iSpecialize ("Y" $! p).
    iRevert "Y".
    iApply wp_initialize_frame. done.
    case_match; eauto. iIntros (?); iApply "X".
  Qed.

  Definition early_destroy : list (decltype * ptr) -> list FreeTemps.t :=
    omap (fun '(ty, p) => if is_trivially_destructible tu ty then Some (FreeTemps.delete ty p) else None).

  (**
     [wp_args eo pre ts_ar es] evaluates [pre ++ es] according to the evaluation order [eo].
     The expressions in [es] are evaluated using initialization semantics for the argument types
     described in [ts_ar] (including handling for variadic functions). The arguments to [Q] are:
     1. the result of evaluating [pre]
     2. the result of evaluating [es]
     3. the immediate destructions, i.e. the object destructions that should occur immediately
        after the function returns.
     4. the delayed destructions, i.e. the destructionst that should occur at the end of the
        full expression. The [FreeTemps] accounts for the correct destruction order.

     Unlike [es], [pre] is expressed directly as a semantic computation in order to unify the
     different ways that it can be used, e.g. to evaluate the object in [o.f()] (which is evaluated
     as a gl-value) or to evaluate the function in [f()] (which is evaluated as a pointer-typed operand).
   *)
  Definition wp_args (eo : evaluation_order.t) (pre : list (wp.WPE.M ptr))
      (ts_ar : list decltype * function_arity) (es : list Expr)
      (Q : list ptr -> list ptr -> FreeTemps -> FreeTemps -> mpred) : mpred :=
    (let '(ts,ar) := ts_ar in
    if check_arity ts ar es then
      let '(tes, va_info) := setup_args ts ar es in
      letI* ps, fs := eval eo (pre ++ map (fun '(t, e) => wp_arg t e) tes) in
        let (pre, ps) := split_at (length pre) ps in
        let early_destroy :=
          FreeTemps.seqs_rev $ early_destroy $ zip_with (fun '(ty, _) p => (ty, p)) tes ps in
        match va_info with
        | Some non_va =>
            let (real, vargs) := split_at non_va ps in
            let types := map fst $ skipn non_va tes in
            let va_info := zip types vargs in
            Forall p, p |-> varargsR va_info -*
                        Q pre (real ++ [p]) (FreeTemps.delete_va va_info p >*> early_destroy)%free fs
        | None =>
            Q pre ps early_destroy fs
        end
    else
      False)%I.

  Lemma wp_args_frame_strong : forall eo pres ts_ar es Q Q',
      ([∗list] m ∈ pres, wp.WPE.Mframe m m)%I
      |-- (Forall ps vs ifree free,
        [| length ps = length pres |] -*
        [| if ts_ar.2 is Ar_Variadic then
             length vs = length ts_ar.1 + 1
           else length vs = length es |] -*
        Q ps vs ifree free -* Q' ps vs ifree free) -*
      wp_args eo pres ts_ar es Q -* wp_args eo pres ts_ar es Q'.
  Proof.
    intros.
    iIntros "PRS X".
    rewrite /wp_args. destruct ts_ar; simpl.
    rewrite /check_arity/setup_args.
    case Nat.compare_spec; intros; try iIntros "[]".
    { rewrite split_at_firstn_skipn.
      iApply (eval_frame_strong with "[PRS]").
      { iSplitL; eauto.
        rewrite big_opL_map.
        iApply big_opL_all.
        iModIntro.
        iIntros (te); destruct te; iApply wp_arg_frame. }
      { iIntros (??) "%".
        rewrite split_at_firstn_skipn.
        revert H0.
        rewrite length_app length_map length_app length_map length_combine length_firstn length_skipn.
        intros. destruct f.
        { iApply "X"; iPureIntro.
          rewrite length_firstn. lia.
          rewrite length_skipn. lia. }
        { rewrite split_at_firstn_skipn.
          iIntros "H" (p) "V".
          iSpecialize ("H" with "V").
          iRevert "H". iApply "X"; iPureIntro.
          - rewrite length_firstn. lia.
          - rewrite length_app length_firstn length_skipn /=. lia. } } }
    { case_bool_decide; try iIntros "[]".
      rewrite split_at_firstn_skipn.
      iApply (eval_frame_strong with "[PRS]").
      { iSplitL; eauto.
        rewrite big_opL_map.
        iApply big_opL_all.
        iModIntro.
        iIntros (te); destruct te; iApply wp_arg_frame. }
      { subst.
        iIntros (?? HH).
        rewrite !split_at_firstn_skipn.
        iIntros "H" (?) "A".
        iSpecialize ("H" with "A").
        revert HH.
        rewrite length_app length_map length_app length_map length_combine length_firstn length_skipn.
        intro.
        iRevert "H"; iApply "X"; iPureIntro.
        - rewrite length_firstn. lia.
        - rewrite length_app length_firstn length_skipn /=. lia. } }
  Qed.

  Lemma wp_args_frame : forall eo pres ts_ar es Q Q',
      ([∗list] m ∈ pres, wp.WPE.Mframe m m)%I
      |-- (Forall ps vs ifree free, Q ps vs ifree free -* Q' ps vs ifree free) -*
          wp_args eo pres ts_ar es Q -* wp_args eo pres ts_ar es Q'.
  Proof.
    intros; iIntros "X Y".
    iApply (wp_args_frame_strong with "X").
    iIntros (??????); iApply "Y".
  Qed.
End with_resolve.

(*
The following definitions describe the "return"-convention.
Specifically, they describe how the returned pointer is received into
the value category that it is called with.

We consolidate these definitions here because they are shared between
all function calls.
*)
Definition xval_receive `{Σ : cpp_logic, σ : genv}
    (ty : exprtype) (res : ptr) (Q : ptr -> epred) : mpred :=
  (**
  [primR] is enough because C++ code never uses the raw bytes
  underlying an inhabitant of a reference type.
  *)
  Exists p, res |-> primR (Tref (erase_qualifiers ty)) 1$m (Vref p) ** Q p.
#[global] Arguments xval_receive {_ _ _ _} _ _ _ / : assert.

Definition lval_receive `{Σ : cpp_logic, σ : genv}
    (ty : exprtype) (res : ptr) (Q : ptr -> epred) : mpred :=
  (**
  [primR] is enough because C++ code never uses the raw bytes
  underlying an inhabitant of a reference type.
  *)
  Exists p, res |-> primR (Tref (erase_qualifiers ty)) 1$m (Vref p) ** Q p.
#[global] Arguments lval_receive {_ _ _ _} _ _ _ / : assert.

mlock Definition operand_receive `{Σ : cpp_logic, σ : genv}
    (ty : exprtype) (res : ptr) (Q : val -> epred) : mpred :=
  Exists v,
  let cv := qual_norm (fun cv _ => cv) ty in
  res |-> tptsto_fuzzyR (erase_qualifiers ty) (cQp.mk (q_const cv) 1) v **
  Q v.

Definition init_receive `{Σ : cpp_logic, σ : genv}
    (addr res : ptr) (Q : epred) : mpred :=
  [| addr = res |] -* Q.
#[global] Arguments init_receive {_ _ _ _} _ _ _ / : assert.

Section receive.
  Context `{Σ : cpp_logic, σ : genv}.

  Lemma xval_receive_frame ty res (Q Q' : ptr -> epred) :
      Forall v, Q v -* Q' v |-- xval_receive ty res Q -* xval_receive ty res Q'.
  Proof.
    rewrite /xval_receive. iIntros "X Y"; iDestruct "Y" as (x) "[? ?]"; iExists x; iFrame; by iApply "X".
  Qed.

  Lemma lval_receive_frame ty res (Q Q' : ptr -> epred) :
      Forall v, Q v -* Q' v |-- lval_receive ty res Q -* lval_receive ty res Q'.
  Proof.
    rewrite /lval_receive. iIntros "X Y"; iDestruct "Y" as (x) "[? ?]"; iExists x; iFrame; by iApply "X".
  Qed.

  Lemma operand_receive_frame ty res (Q Q' : val -> epred) :
      Forall v, Q v -* Q' v |-- operand_receive ty res Q -* operand_receive ty res Q'.
  Proof.
    rewrite operand_receive.unlock. iIntros "X Y"; iDestruct "Y" as (x) "[? ?]"; iExists x; iFrame; by iApply "X".
  Qed.

  Lemma init_receive_frame addr res (Q Q' : epred) :
      Q -* Q' |-- init_receive addr res Q -* init_receive addr res Q'.
  Proof.
    rewrite /init_receive. iIntros "X Y Z"; iApply "X"; iApply "Y"; done.
  Qed.
End receive.
