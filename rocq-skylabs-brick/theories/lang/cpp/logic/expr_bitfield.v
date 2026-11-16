(*
 * Copyright (C) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(** * Semantics of expressions on bit-fields

    A bit-field has no address, so no rule of [wp_lval], [wp_xval] or
    [wp_glval] applies to a bit-field access [Ebitfield]. Glvalues that may
    denote a bit-field are evaluated by [wp_bitfield_glval] (see ../logic/wp.v),
    which yields the pointer to the enclosing object and, for a bit-field,
    a [bf_designator].

    The rules are:
    - the leaf rule for [Ebitfield];
    - the embedding of ordinary glvalues, with no designator;
    - rules for the parents whose result is a bit-field when their glvalue
      operand is: comma, conditional, assignment, compound assignment,
      pre-increment and pre-decrement ([is_bitfield] follows the same ones);
    - for the consumers of such glvalues, the lvalue-to-rvalue conversion,
      post-increment and post-decrement, a rule next to the existing one.
      Discarded-value expressions use [wp_bitfield_glval] directly (see
      [wp_discard]).

    Each rule evaluates its operands exactly like the existing rule for the
    same construct, and its access to an ordinary object ([None]) is exactly
    the existing one. Existing rules are unchanged. *)
Require Import skylabs.prelude.base.
Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import skylabs.iris.extra.bi.errors.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.lang.cpp.logic.pred.
Require Import skylabs.lang.cpp.logic.path_pred.
Require Import skylabs.lang.cpp.logic.heap_pred.
Require Import skylabs.lang.cpp.logic.operator.
Require Import skylabs.lang.cpp.logic.wp.
Require Import skylabs.lang.cpp.logic.expr.
Require Import skylabs.lang.cpp.logic.bitfield.

#[local] Open Scope free_scope.

Module bitfield_expr.

  (** [info_ok info ty] checks that [info] describes a bit-field of declared
      type [ty] as cpp2v emits it: a standard integer type of the recorded
      signedness, and a nonzero width no larger than that type's. Then the
      values in range for [info] are values of type [ty]. *)
  Definition info_ok (info : BitfieldInfo) (ty : type) : bool :=
    bool_decide (drop_qualifiers ty = drop_qualifiers info.(bf_type)) &&
    match drop_qualifiers info.(bf_type) with
    | Tnum sz sgn =>
        bool_decide (sgn = info.(bf_signed)) &&
        bool_decide (info.(bf_width) <> 0)%N &&
        bool_decide (info.(bf_width) <= bitsize.bitsN (int_rank.bitsize sz))%N
    | _ => false
    end.

  (** [promoted_type tu info] is the type to which the integral promotions
      convert a value of the bit-field [info]
      (<https://eel.is/c++draft/conv.prom#5>): <<int>> if it can represent
      all values of the bit-field, otherwise <<unsigned int>> if it can, and
      otherwise the promotion of the declared type. *)
  Definition promoted_type (tu : translation_unit) (info : BitfieldInfo) : option type :=
    let int_bits := bitsize.bitsN (int_rank.bitsize int_rank.Iint) in
    let w := info.(bf_width) in
    match info.(bf_signed) with
    | Signed =>
        if bool_decide (w <= int_bits)%N then Some Tint
        else promote_integral tu info.(bf_type)
    | Unsigned =>
        if bool_decide (w < int_bits)%N then Some Tint
        else if bool_decide (w <= int_bits)%N then Some Tuint
        else promote_integral tu info.(bf_type)
    end.

End bitfield_expr.

(** ** Access primitives

    [r : ptr * option bf_designator] is the result of [wp_bitfield_glval]:
    [(p, Some d)] for the bit-field [d] of the object at [p], [(p, None)] for
    the ordinary object at [p]. *)
Section access.
  Context `{Σ : cpp_logic} {σ : genv} (tu : translation_unit).

  (** [bf_read ty r Q] reads the value of [r], of erased type [ty]. For an
      ordinary object this is the body of [wp_operand_cast_l2r]. *)
  Definition bf_read (ty : type) (r : ptr * option bf_designator) (Q : val -> mpred) : mpred :=
    match r with
    | (p, None) =>
        Exists v, (Exists q, p |-> initializedR ty q v ** True) //\\ Q v
    | (p, Some d) =>
        Exists q cs m v,
          (p |-> bitfieldsR d.(bfd_cls) d.(bfd_info).(bf_run) q cs m **
           [| m !! d.(bfd_field) = Some v |] ** True) //\\
          Q (Vint v)
    end.

  (** [bf_write ty r rv Q] stores [rv] into [r], of erased type [ty], then
      continues as [Q]. For an ordinary object this is the body of
      [wp_lval_assign]. A bit-field needs its whole memory location, and
      stores the value reduced to its width. *)
  Definition bf_write (ty : type) (r : ptr * option bf_designator) (rv : val) (Q : mpred) : mpred :=
    match r with
    | (p, None) =>
        p |-> anyR ty 1$m ** (p |-> tptstoR ty 1$m rv -* Q)
    | (p, Some d) =>
        let cls := d.(bfd_cls) in
        let run := d.(bfd_info).(bf_run) in
        let f := d.(bfd_field) in
        Exists z cs m,
          [| rv = Vint z |] ** [| cs !! f = Some false |] **
          p |-> bitfieldsR cls run 1 cs m **
          (p |-> bitfieldsR cls run 1 cs
                   (<[f := bitfield.trunc d.(bfd_info).(bf_signed) d.(bfd_info).(bf_width) z]> m)
           -* Q)
    end.

  (** [bf_update pty ty r v v' Q] replaces the value [v] of [r], of erased
      type [ty], by [v'] (reduced to the width of a bit-field), then
      continues as [Q]. For an ordinary object this is the [primR] update of
      [wp_lval_bop_assign], [pre_op] and [post_op].

      [v'] was computed after promoting [v] as a value of type [pty]. The
      integral promotions of a bit-field depend on its width
      (<https://eel.is/c++draft/conv.prom#5>), so for a bit-field this
      requires them to agree with those of [pty]. *)
  Definition bf_update (pty ty : type) (r : ptr * option bf_designator) (v v' : val) (Q : mpred) : mpred :=
    match r with
    | (p, None) =>
        p |-> primR ty 1$m v ** (p |-> primR ty 1$m v' -* Q)
    | (p, Some d) =>
        let cls := d.(bfd_cls) in
        let run := d.(bfd_info).(bf_run) in
        let f := d.(bfd_field) in
        Exists z z' cs m,
          [| bitfield_expr.promoted_type tu d.(bfd_info) = promote_integral tu pty |] **
          [| v = Vint z |] ** [| v' = Vint z' |] **
          [| m !! f = Some z |] ** [| cs !! f = Some false |] **
          p |-> bitfieldsR cls run 1 cs m **
          (p |-> bitfieldsR cls run 1 cs
                   (<[f := bitfield.trunc d.(bfd_info).(bf_signed) d.(bfd_info).(bf_width) z']> m)
           -* Q)
    end.
End access.

Module Type Expr__bitfield.

  Section with_resolve.
    Context `{Σ : cpp_logic} {resolve:genv}.
    Variables (tu : translation_unit) (ρ : region).

    #[local] Notation wp_glval := (wp_glval tu ρ).
    #[local] Notation wp_operand := (wp_operand tu ρ).
    #[local] Notation wp_discard := (wp_discard tu ρ).
    #[local] Notation wp_bitfield_glval := (wp_bitfield_glval tu ρ).
    #[local] Notation read_arrow := (read_arrow tu ρ).
    #[local] Notation wp_cond := (wp_cond tu ρ).
    #[local] Notation inc_dec_op := (inc_dec_op tu).
    #[local] Notation bf_update := (bf_update tu).

    (** The leaf: <<a.f>> (<<a->f>> if [arrow]) for a bit-field [f] that the
        translation unit describes. It designates [f] of the object [a]
        denotes; neither [a] nor [f] is accessed. Compare [wp_lval_member]. *)
    Axiom wp_bitfield_glval_member : forall arrow a f ty vc cv cls info Q,
        arrow_aggregate_type arrow (decltype_of_expr a) = Some (vc, cv, cls) ->
        bitfield_lookup tu cls f = Some info ->
        bitfield_expr.info_ok info ty = true ->
          (letI* base, free := read_arrow arrow a in
           Q (base, Some (Build_bf_designator cls f info)) free)
      |-- wp_bitfield_glval (Ebitfield arrow a f ty) Q.

    (** Every glvalue that [wp_glval] evaluates denotes an ordinary object. *)
    Axiom wp_bitfield_glval_glval : forall e Q,
        wp_glval e (fun p free => Q (p, None) free)
      |-- wp_bitfield_glval e Q.

    (** <<e1, e2>>: compare [wp_lval_comma]. *)
    Axiom wp_bitfield_glval_comma : forall e1 e2 Q,
        wp_discard e1 (fun free1 => wp_bitfield_glval e2 (fun r free2 => Q r (free2 >*> free1)))
      |-- wp_bitfield_glval (Ecomma e1 e2) Q.

    (** <<c ? e1 : e2>>: compare [wp_lval_condition]. Each arm is evaluated
        by [wp_bitfield_glval], so the result may designate a bit-field or
        not, depending on [c]. *)
    Axiom wp_bitfield_glval_condition : Reduce (wp_cond wp_bitfield_glval).

    (** <<l = r>>: compare [wp_lval_assign]. The result designates [l]. *)
    Axiom wp_bitfield_glval_assign : forall ty l r Q,
        (letI* '(lr, rv), free :=
           eval2 (evaluation_order.order_of (language_version tu) OOEqual)
             (wp_bitfield_glval l) (wp_operand r) in
         bf_write (erase_qualifiers ty) lr rv (Q lr free))
      |-- wp_bitfield_glval (Eassign l r ty) Q.

    (** <<l op= r>>: compare [wp_lval_bop_assign]. *)
    Axiom wp_bitfield_glval_bop_assign : forall ty o oo l r Q,
        to_operator_equal o = Some oo ->
        match convert_type_op tu o (type_of l) (type_of r) with
        | Some (tl, tr, resultT) =>
          letI* '(lr, rv), free :=
            eval2 (evaluation_order.order_of (language_version tu) oo)
              (wp_bitfield_glval l) (wp_operand r) in
          Exists lv clv resv storedv,
            ([| convert tu (type_of l) tl lv clv |] **
             [| tr = type_of r |] **
             eval_binop tu o tl tr resultT clv rv resv **
             [| convert tu resultT ty resv storedv |] ** True) //\\
            bf_update (type_of l) (erase_qualifiers ty) lr lv storedv (Q lr free)
        | _ => False%I
        end
      |-- wp_bitfield_glval (Eassign_op o l r ty) Q.

    (** Pre-increment and pre-decrement: compare [pre_op]. *)
    Definition bf_pre_op (b : BinOp) (ty : type) (e : Expr)
        (Q : ptr * option bf_designator -> FreeTemps.t -> mpred) : mpred :=
      let ety := erase_qualifiers $ type_of e in
      wp_bitfield_glval e (fun r free => Exists v v',
        (inc_dec_op b ety v v' ** True) //\\
        bf_update ety ety r v v' (Q r free)).

    (** <<++e>>: compare [wp_lval_preinc]. *)
    Axiom wp_bitfield_glval_preinc : forall e ty Q,
        bf_pre_op Badd ty e Q |-- wp_bitfield_glval (Epreinc e ty) Q.

    (** <<--e>>: compare [wp_lval_predec]. *)
    Axiom wp_bitfield_glval_predec : forall e ty Q,
        bf_pre_op Bsub ty e Q |-- wp_bitfield_glval (Epredec e ty) Q.

    (** ** Consumers *)

    (** The lvalue-to-rvalue conversion: compare [wp_operand_cast_l2r]. *)
    Axiom wp_operand_cast_l2r_bitfield : forall e Q,
        (letI* r, free := wp_bitfield_glval e in
         bf_read (erase_qualifiers $ type_of e) r (fun v => Q v free))
      |-- wp_operand (Ecast Cl2r e) Q.

    (** Post-increment and post-decrement: compare [post_op]. The value is
        the old one. *)
    Definition bf_post_op (b : BinOp) (ty : type) (e : Expr)
        (Q : val -> FreeTemps.t -> mpred) : mpred :=
      let ety := erase_qualifiers $ type_of e in
      wp_bitfield_glval e (fun r free => Exists v v',
        (inc_dec_op b ety v v' ** True) //\\
        bf_update ety ety r v v' (Q v free)).

    (** <<e++>>: compare [wp_operand_postinc]. *)
    Axiom wp_operand_postinc_bitfield : forall e ty Q,
        bf_post_op Badd ty e Q |-- wp_operand (Epostinc e ty) Q.

    (** <<e-->>: compare [wp_operand_postdec]. *)
    Axiom wp_operand_postdec_bitfield : forall e ty Q,
        bf_post_op Bsub ty e Q |-- wp_operand (Epostdec e ty) Q.

  End with_resolve.
End Expr__bitfield.

Declare Module E__bitfield : Expr__bitfield.

Export E__bitfield.
