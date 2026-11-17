(*
 * Copyright (c) 2020-2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import elpi.apps.locker.locker.
Require Import skylabs.iris.extra.proofmode.proofmode.	(** Early to get the right [ident] *)
Require Import skylabs.iris.extra.bi.ChargeCompat.
Require Import skylabs.iris.extra.bi.errors.
Require Import skylabs.lang.cpp.logic.entailsN.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.lang.cpp.logic.rep_proofmode.

Require Import skylabs.lang.cpp.logic.pred.
Require Import skylabs.lang.cpp.logic.path_pred.
Require Import skylabs.lang.cpp.logic.heap_pred.
Require Import skylabs.lang.cpp.logic.wp.
Require Import skylabs.lang.cpp.logic.builtins.
Require Import skylabs.lang.cpp.logic.cptr.
Require Import skylabs.lang.cpp.logic.const.
Require Import skylabs.lang.cpp.logic.initializers.
Require Import skylabs.lang.cpp.logic.translation_unit.
Require Import skylabs.lang.cpp.logic.destroy.
Require Import skylabs.lang.cpp.logic.call.
Require Import skylabs.lang.cpp.logic.raw.

(* UPSTREAM. *)
Lemma wand_frame {PROP : bi} (R Q Q' : PROP) :
  Q -* Q' |-- (R -* Q) -* (R -* Q').
Proof. iIntros "Q W R". iApply ("Q" with "(W R)"). Qed.

#[local] Set Printing Coercions.

#[local] Arguments ERROR {_ _} _%_bs.
#[local] Arguments UNSUPPORTED {_ _} _%_bs.
#[local] Arguments wpi : simpl never.

#[local] Remove Hints Ar_Definite CC_C : typeclass_instances.

(**
[Kreturn ty Q] is the continuation of the body of a function or method
whose declared return type is [ty].

A function returning cv <<void>> may <<return;>> or fall off the end
([stmt.return]); the result object then carries the constness of [cv],
matching the fraction [cQp.mk (q_const cv) 1] that callers receive.
Normal completion of a non-void function is undefined behavior. The frontend
makes the implicit <<return 0;>> at the end of <<main>> explicit.
*)
Definition Kreturn_inner `{Σ : cpp_logic, σ : genv} (ty : type) (Q : ptr -> mpred) (rt : ReturnType) : mpred :=
  match rt with
  | Normal | ReturnVoid =>
    match drop_qualifiers ty with
    | Tvoid => Forall p : ptr, p |-> primR Tvoid (cQp.mk (q_const (take_qualifiers ty)) 1) Vvoid -* Q p
    | _ => ERROR "Kreturn: normal completion of a non-void function"
    end
  | ReturnVal p => Q p
  (* [ReturnNRVO] must have been turned into [ReturnVal] by the [Kfree] of the
     scope declaring the variable: reaching the function boundary means the
     returned name was not an automatic variable of this function. *)
  | Break | Continue | ReturnNRVO _ _ => False
  (* A [goto] whose label no enclosing block found (see [Kblock] and
     [Klabels]): into a nested statement, forward past a declaration, or
     back in a <<switch>> body to before the <<case>> that was entered. *)
  | Goto _ => False
  end.
#[global] Arguments Kreturn_inner _ _ _ _ _ _ !rt /.

Definition Kreturn `{Σ : cpp_logic, σ : genv} (ty : type) (Q : ptr -> mpred) : Kpred :=
  KP $ Kreturn_inner ty Q.
#[global] Hint Opaque Kreturn : typeclass_instances.

Section Kreturn.
  Context `{Σ : cpp_logic, σ : genv}.

  Lemma Kreturn_frame ty (Q Q' : ptr -> mpred) (rt : ReturnType) :
    Forall p, Q p -* Q' p
                |-- Kreturn ty Q rt -* Kreturn ty Q' rt.
  Proof.
    iIntros "HQ". destruct rt; cbn; try case_match; auto.
    all: iIntros "HR" (?) "R"; iApply "HQ"; by iApply "HR".
  Qed.
End Kreturn.

(** ** Weakest precondition of a constructor: Initial construction step. *)
(**
Makes [this] and immediate [members] of [cls] strictly valid, to
implement the part of http://eel.is/c++draft/class.cdtor#3 about
members. This enables their dereference via [wp_lval_deref].
*)
mlock Definition svalid_members `{Σ : cpp_logic, σ : genv}
    (cls : globname) (members : list (field_name.t * type)) : Rep :=
  reference_toR (Tnamed cls) **
  [** list] m ∈ members, _field (Field cls m.1) |-> reference_toR m.2.

Section svalid_members.
  Context `{Σ : cpp_logic, σ : genv}.

  #[global] Instance svalid_members_persistent : Persistent2 svalid_members.
  Proof. rewrite svalid_members.unlock. apply _. Qed.

  #[global] Instance svalid_members_affine : Affine2 svalid_members := _.
End svalid_members.

(** ** Aggregate identity *)
(**
[settle_path settled path] is the path of an identity token: [path] for a
settled token, and [nil] for an unsettled one.  A token with the empty path
gives virtual dispatch nothing to dispatch on ([resolve_virtual] requires a
non-empty path), so an unsettled subobject supports conversions but no virtual
calls.  [struct_defR] holds such tokens before construction, and
[mdc_path_forget] produces them.
*)
Definition settle_path (settled : bool) (path : list globname) : list globname :=
  if settled then path else nil.

(**
Part of [derivationsR path cls], but indexed by fuel [f].

TODO: Replace this with a version that is built by well-founded
recursion.
*)
#[local]
Definition derivationsR' `{Σ : cpp_logic, σ : genv} (tu : translation_unit) (q : cQp.t)
    (settled : bool) :=
  fix derivationsR' (f : nat) (include_base : bool) (cls : globname) (path : list globname) : Rep :=
  match f with
  | 0 => ERROR "derivationsR: no fuel"
  | S f =>
    match tu.(types) !! cls with
    | Some (Gstruct st) =>
      (if include_base && has_vtable st then derivationR cls (settle_path settled path) q else emp) **
      [** list] b ∈ st.(s_bases),
      let base := b.1 in
      _base cls base |-> derivationsR' f true base (path ++ [base])
    | _ => ERROR "derivationsR: not a structure"
    end
  end.

(**
[this |-> derivationsR tu include_base cls path q] is all of the
object identities of the [this] object (of type [cls]) where the most
derived class is reached from [cls] using [path]. For example,
consider the following:
<<
class A {};
class B : public A {};
class C : public B {};
>>
here, [derivationsR true "::B" ["::C"] q] produces:
[[
derivationR "::B" ["::C","::B"] q **
_base "::B" "::A" |-> derivationR "::A" ["::C","::B","::A"] q
]]

while [derivationsR true "::C" [] q] produces all the identities for
<<A>>, <<B>> and <<C>>:
[[
derivationR "::C" ["::C"] q **
_base "::C" "::B" |-> derivationR true "::B" ["::C"] q
]]
*)
Definition derivationsR `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (include_base : bool) (cls : globname) (path : list globname) (q : cQp.t) : Rep :=
  (**
  The number of global entries is an upper bound on the height of the
  derivation tree.
  *)
  let size := NM.cardinal σ.(genv_tu).(types) in
  derivationsR' tu q true size include_base cls path.

(**
[this |-> unsettledR tu include_base cls q] is the identity tokens of the
[this] object (of type [cls]) and of its bases, all *unsettled*: each has the
empty path (see [settle_path]), so no virtual call through them is possible.
A base subobject is in this state after its own constructor returns and
before the enclosing constructor sets the identity of the whole object
([wp_init_identity]), and in a destructor from the end of the member
destruction until right before that base's destructor ([wp_settle_identity]).
*)
Definition unsettledR `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (include_base : bool) (cls : globname) (q : cQp.t) : Rep :=
  let size := NM.cardinal σ.(genv_tu).(types) in
  derivationsR' tu q false size include_base cls [].

Section derivationsR.
  Context `{Σ : cpp_logic, σ : genv}.

  Lemma derivationsR'_sub_module tu tu' q settled f include_base cls path :
    sub_module tu tu' ->
    derivationsR' tu q settled f include_base cls path
    |-- derivationsR' tu' q settled f include_base cls path.
  Proof.
    intros Hsub%types_compat.
    move: include_base cls path. induction f; intros; cbn; first done.
    case_match eqn:Hcls; last by rewrite {1}ERROR_elim; apply bi.False_elim.
    specialize (Hsub _ _ Hcls). destruct Hsub as (gv' & Heq & Hsub); rewrite Heq; clear Heq.
    case_match; try by rewrite {1}ERROR_elim; apply bi.False_elim.
    destruct gv'; try done. cbn in Hsub. case_bool_decide; [simplify_eq|done].
    f_equiv. f_equiv=>_ b. f_equiv. apply IHf.
  Qed.

  Lemma derivationsR_sub_module tu tu' q include_base cls path :
    sub_module tu tu' ->
    derivationsR tu q include_base cls path
    |-- derivationsR tu' q include_base cls path.
  Proof. apply derivationsR'_sub_module. Qed.

  (* [supports_with_fuel tu cls f] states that [f] is sufficient fuel to cover
     the entire class hierarchy of [cls] within the translation unit [tu].

     This is the pure part of [derivationsR] *)
  Inductive supports_with_fuel (tu : translation_unit) (cls : globname) : nat -> Prop :=
  | supports_S {f st}
      (_ : tu.(types) !! cls = Some (Gstruct st))
      (_ : List.Forall (fun b => supports_with_fuel tu b.1 f) st.(s_bases))
    : supports_with_fuel tu cls (S f).

  Lemma supports_big_op (PROP : bi) tu cls st f :
    (tu.(types) !! cls = Some (Gstruct st)) ->
    ([∗list] b ∈ st.(s_bases) , [| supports_with_fuel tu b.1 f |]) |-@{PROP} [| supports_with_fuel tu cls (S f) |].
  Proof.
    intros.
    iPureIntro. intros.
    econstructor; eauto.
    apply List.Forall_forall. intros.
    apply list_elem_of_In in H1.
    apply list_elem_of_lookup_1 in H1.
    destruct H1.
    eapply H0; eauto.
  Qed.

  Lemma derivationsR'_ok tu tu' (sub : sub_module tu tu') :
    forall settled f f' mdc (p : ptr) cls include_base q,
    f <= f' ->
        p |-> derivationsR' tu q settled f include_base cls mdc
    |-- p |-> derivationsR' tu' q settled f' include_base cls mdc ** [| supports_with_fuel tu cls f |].
  Proof.
    induction f; rewrite /derivationsR' /=; intros; try iIntros "[]".
    destruct f'; try lia.
    case_match; try by iIntros "[]".
    case_match; try by iIntros "[]".
    erewrite sub_module_preserves_gstruct; eauto.
    subst. rewrite !_at_sep.
    rewrite -!bi.sep_assoc.
    iIntros "[X Y]". iSplitL "X".
    { case_match; try rewrite _at_emp; eauto. }
    rewrite -supports_big_op; eauto.
    rewrite !_at_big_sepL.
    rewrite -big_sepL_sep.
    iRevert "Y".
    iApply big_sepL_mono.
    intros.
    rewrite !_at_offsetR.
    rewrite (IHf f'); last lia.
    eauto.
  Qed.

  Lemma derivationsR_ok tu tu' (sub : sub_module tu tu') :
    forall mdc (p : ptr) cls include_base q,
        p |-> derivationsR tu include_base cls mdc q
    |-- p |-> derivationsR tu' include_base cls mdc q ** [| supports_with_fuel tu cls (NM.cardinal (types $ genv_tu σ)) |].
  Proof. intros; by apply derivationsR'_ok; eauto. Qed.

  Lemma unsettledR_ok tu tu' (sub : sub_module tu tu') :
    forall (p : ptr) cls include_base q,
        p |-> unsettledR tu include_base cls q
    |-- p |-> unsettledR tu' include_base cls q ** [| supports_with_fuel tu cls (NM.cardinal (types $ genv_tu σ)) |].
  Proof. intros; by apply derivationsR'_ok; eauto. Qed.

  Lemma derivationsR'_ok_supports tu tu' (sub : sub_module tu tu') :
    forall cls f, supports_with_fuel tu cls f ->
             forall settled f' mdc (p : ptr) include_base q, f <= f' ->
        p |-> derivationsR' tu q settled f include_base cls mdc
    -|- p |-> derivationsR' tu' q settled f' include_base cls mdc.
  Proof.
    refine (fix rec cls f X {struct X} :=
              match X with
              | supports_S _ _ _ _ => _
              end); simpl; intros.
    destruct f'; try lia. simpl.
    rewrite e.
    erewrite sub_module_preserves_gstruct; eauto.
    rewrite !_at_sep !_at_big_sepL. f_equiv.
    induction f0; simpl; eauto.
    rewrite IHf0 !_at_offsetR. f_equiv.
    iApply rec; eauto. lia.
  Qed.

  Lemma derivationsR_ok_supports tu tu' (sub : sub_module tu tu') :
    forall cls, supports_with_fuel tu cls (NM.cardinal (types (genv_tu σ))) ->
             forall mdc (p : ptr) include_base q,
        p |-> derivationsR tu include_base cls mdc q
    -|- p |-> derivationsR tu' include_base cls mdc q.
  Proof.
    intros.
    rewrite /derivationsR.
    eapply derivationsR'_ok_supports; eauto.
  Qed.

  Lemma unsettledR_ok_supports tu tu' (sub : sub_module tu tu') :
    forall cls, supports_with_fuel tu cls (NM.cardinal (types (genv_tu σ))) ->
             forall (p : ptr) include_base q,
        p |-> unsettledR tu include_base cls q
    -|- p |-> unsettledR tu' include_base cls q.
  Proof.
    intros.
    rewrite /unsettledR.
    eapply derivationsR'_ok_supports; eauto.
  Qed.

End derivationsR.

(* conveniences for the common pattern *)
Notation init_derivationR cls path q :=
  (derivationR cls%_cpp_name (path%_cpp_name ++ [cls%_cpp_name]) q).

(**
The identity of an object of class [cls] goes through these states:

- During construction, each base constructor returns its base's identity
  settled with that base as most-derived class.  [wp_unsettle_identity]
  makes it unsettled right away, and [wp_init_identity] settles the identity
  of the whole object only after all bases are initialized.  In between, a
  virtual call through an already-built base is undefined: from the
  constructor's own ctor-initializer ([class.base.init]/18), or from a later
  base's constructor, of which the earlier base is no base
  ([class.cdtor]/4).  Compilers disagree there: Clang writes the derived
  class's vptrs before a base initializer that mentions [this], GCC after
  all bases.  So the rules allow no dispatch.
- During destruction, the members are destroyed with the identity settled
  for [cls] ([class.cdtor]/4 makes calls from member destructors dispatch in
  [cls]).  Then [wp_revert_identity] unsettles every base, and right before
  each base's destructor [wp_settle_identity] settles that base's identity
  with the base as most-derived class.  A call through a base whose
  destructor has not started yet, from the destructor of another base, is
  undefined ([class.cdtor]/4).

Unsettled tokens still witness the subobjects for conversions, which need no
identity.
*)

(**
[wp_init_identity this tu cls Q] sets the identity of [this] (of class
[cls]) and of all its bases (transitively), which must be unsettled, to
[cls] as most-derived class.
*)
Definition wp_init_identity `{Σ : cpp_logic, σ : genv} (p : ptr) (tu : translation_unit)
    (cls : globname) (Q : mpred) : mpred :=
  p |-> unsettledR tu false cls 1$m **
  (p |-> derivationsR tu true cls [cls] 1$m -* Q).

(**
[wp_unsettle_identity this tu b Q] runs right after the constructor of the
base subobject [this] (of class [b]) returns: it takes the identity that
constructor established, with [b] as most-derived class, and makes it
unsettled.
*)
Definition wp_unsettle_identity `{Σ : cpp_logic, σ : genv} (p : ptr) (tu : translation_unit)
    (b : globname) (Q : mpred) : mpred :=
  p |-> derivationsR tu true b [b] 1$m **
  (p |-> unsettledR tu true b 1$m -* Q).

(**
[wp_revert_identity this tu cls Q] runs in the destructor of [this] (of
class [cls]) after the members are destroyed: it takes the identity of
[this] and of its bases, with [cls] as most-derived class, drops [cls]'s own
token, and leaves the bases unsettled.
*)
Definition wp_revert_identity `{Σ : cpp_logic, σ : genv} (p : ptr) (tu : translation_unit)
    (cls : globname) (Q : mpred) : mpred :=
  p |-> derivationsR tu true cls [cls] 1$m **
  (p |-> unsettledR tu false cls 1$m -* Q).

(**
[wp_settle_identity this tu b Q] runs in a destructor right before the
destructor of the base subobject [this] (of class [b]): it settles the
identity of [this] and its bases with [b] as most-derived class, which is
what [b]'s destructor expects.
*)
Definition wp_settle_identity `{Σ : cpp_logic, σ : genv} (p : ptr) (tu : translation_unit)
    (b : globname) (Q : mpred) : mpred :=
  p |-> unsettledR tu true b 1$m **
  (p |-> derivationsR tu true b [b] 1$m -* Q).

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (p : ptr) (Q : mpred).

  Lemma wp_init_identity_frame p tu tu' cls Q Q' :
    sub_module tu tu' ->
    Q' -* Q |-- wp_init_identity p tu cls Q' -* wp_init_identity p tu' cls Q.
  Proof.
    rewrite /wp_init_identity.
    iIntros (sub) "Q [X Y]".
    iDestruct (unsettledR_ok with "X") as "[X %]"; eauto.
    iFrame.
    iIntros "X". iApply "Q".
    iApply "Y".
    iApply derivationsR_ok_supports; eauto.
  Qed.

  Lemma wp_unsettle_identity_frame p tu tu' cls Q Q' :
    sub_module tu tu' ->
    Q' -* Q |-- wp_unsettle_identity p tu cls Q' -* wp_unsettle_identity p tu' cls Q.
  Proof.
    rewrite /wp_unsettle_identity.
    iIntros (sub) "Q [X Y]".
    iDestruct (derivationsR_ok with "X") as "[X %]"; eauto.
    iFrame.
    iIntros "X". iApply "Q".
    iApply "Y".
    iApply unsettledR_ok_supports; eauto.
  Qed.

  Lemma wp_revert_identity_frame p tu tu' cls Q Q' :
    sub_module tu tu' ->
    Q' -* Q |-- wp_revert_identity p tu cls Q' -* wp_revert_identity p tu' cls Q.
  Proof.
    rewrite /wp_revert_identity.
    iIntros (sub) "Q [X Y]".
    iDestruct (derivationsR_ok with "X") as "[X %]"; eauto.
    iFrame.
    iIntros "X". iApply "Q".
    iApply "Y".
    iApply unsettledR_ok_supports; eauto.
  Qed.

  Lemma wp_settle_identity_frame p tu tu' cls Q Q' :
    sub_module tu tu' ->
    Q' -* Q |-- wp_settle_identity p tu cls Q' -* wp_settle_identity p tu' cls Q.
  Proof.
    rewrite /wp_settle_identity.
    iIntros (sub) "Q [X Y]".
    iDestruct (unsettledR_ok with "X") as "[X %]"; eauto.
    iFrame.
    iIntros "X". iApply "Q".
    iApply "Y".
    iApply derivationsR_ok_supports; eauto.
  Qed.

  (** sanity check that initialization and revert are inverses *)
  Lemma wp_init_revert p tu cls Q :
    let REQ := p |-> unsettledR tu false cls 1$m in
    REQ ** Q
    |-- wp_init_identity p tu cls (wp_revert_identity p tu cls (REQ ** Q)).
  Proof.
    rewrite /wp_revert_identity/wp_init_identity.
    iIntros "[$ $] $ $".
  Qed.

  (** and so are unsettling and settling a base *)
  Lemma wp_unsettle_settle p tu b Q :
    let REQ := p |-> derivationsR tu true b [b] 1$m in
    REQ ** Q
    |-- wp_unsettle_identity p tu b (wp_settle_identity p tu b (REQ ** Q)).
  Proof.
    rewrite /wp_unsettle_identity/wp_settle_identity.
    iIntros "[$ $] $ $".
  Qed.
End with_cpp.

(** ** Binding parameters *)

Definition wp_make_mutables `{Σ : cpp_logic, σ : genv} (tu : translation_unit) :=
  fix wp_make_mutables (args : list (ptr * decltype)) (Q : epred) : mpred :=
  match args with
  | nil => Q
  | p :: args => wp_make_mutables args $ wp_make_mutable tu p.1 p.2 Q
  end.
#[global] Hint Opaque wp_make_mutables : typeclass_instances.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (Q : epred).

  Lemma wp_make_mutables_frame tu tu' args Q Q' :
    sub_module tu tu' ->
    Q -* Q' |-- wp_make_mutables tu args Q -* wp_make_mutables tu' args Q'.
  Proof.
    intros ?%types_compat.
    move: Q Q'. induction args; intros; first done. cbn. iIntros "HQ".
    iApply (IHargs with "[HQ]"). by iApply wp_const_frame.
  Qed.
End with_cpp.

Definition Kcleanup `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (args : list (ptr * decltype)) (Q : Kpred) : Kpred :=
  Kat_exit (wp_make_mutables tu args) Q.
#[global] Hint Opaque Kcleanup : typeclass_instances.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (Q : Kpred).

  Lemma Kcleanup_frame tu tu' args (Q Q' : Kpred) rt :
    sub_module tu tu' ->
    Q rt -* Q' rt |-- Kcleanup tu args Q rt -* Kcleanup tu' args Q' rt.
  Proof.
    intros. rewrite /Kcleanup. iIntros "?". iApply Kat_exit_frame; [|done].
    iIntros (??) "?". by iApply wp_make_mutables_frame.
  Qed.
End with_cpp.

(**
[bind_vars tu ar ts args ρ Q] initializes a function's arguments
[args] according to its arity [ar] and declared parameter types [ts].

NOTE. We make arguments [const] here if necessary and then make them
mutable again in the second argument to [Q].
*)
Definition bind_vars `{Σ : cpp_logic, σ : genv} (tu : translation_unit) (ar : function_arity) :=
  fix bind_vars (ts : list (ident * decltype)) (args : list ptr)
    (ρ : option ptr -> region) (Q : region -> list (ptr * decltype) -> epred) : mpred :=
  match ts with
  | nil =>
    match ar with
    | Ar_Definite =>
      match args with
      | nil => Q (ρ None) []
      | _ :: _ => ERROR "bind_vars: extra arguments"
      end
    | Ar_Variadic =>
      match args with
      | vap :: nil => Q (ρ $ Some vap) []
      | _ => ERROR "bind_vars: variadic function missing varargs"
      end
    end
  | xty :: ts =>
    match args with
    | p :: args =>
      (*
      NOTE: We need not gather additional qualifiers from an array's
      element type as Clang's parser eagerly "decays" a function's
      array parameter types to pointer types.
      *)
      let recurse := bind_vars ts args (fun vap => Rbind xty.1 p $ ρ vap) in
      let qty := decompose_type xty.2 in
      let ty := qty.2 in
      if q_const qty.1 then
        let* := wp_make_const tu p ty in
        let* ρ, consts := recurse in
        Q ρ $ (p,ty) :: consts
      else
        recurse Q
    | nil => ERROR "bind_vars: insufficient arguments"
    end
  end.
#[global] Hint Opaque bind_vars : typeclass_instances.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (Q : region -> list (ptr * decltype) -> epred).

  Lemma bind_vars_frame tu tu' ar ts args ρ Q Q' :
    sub_module tu tu' ->
    Forall ρ args', Q ρ args' -* Q' ρ args'
    |-- bind_vars tu ar ts args ρ Q -* bind_vars tu' ar ts args ρ Q'.
  Proof.
    intros Hsub%types_compat. move: args ρ Q Q'. induction ts; intros [] *; cbn.
    { destruct ar; auto. iIntros "HQ ?". by iApply "HQ". }
    { destruct ar; auto. case_match; auto. iIntros "HQ ?". by iApply "HQ". }
    { auto. }
    { iIntros "HQ". case_match.
      - iApply wp_const_frame; [done|]. iApply IHts. iIntros (??) "?". by iApply "HQ".
      - iApply IHts. iIntros (??) "?". by iApply "HQ". }
  Qed.
End with_cpp.

(** ** The weakest precondition of a function *)

(**
NOTE: The fancy updates in `wp_func` and friends are not in the right
place to support `XX_shift` lemmas. This could be fixed.
*)
#[local] Definition wp_func' `{Σ : cpp_logic, σ : genv} (u : bool) (tu : translation_unit)
    (f : Func) (args : list ptr) (Q : ptr -> epred) : mpred :=
  match f.(f_body) with
  | None => ERROR "wp_func: no body"
  | Some body =>
    match body with
    | Impl body =>
      let ρ vap := Remp None vap f.(f_return) in
      letI* ρ, cleanup := bind_vars tu f.(f_arity) f.(f_params) args ρ in
      |> wp tu ρ body (Kcleanup tu cleanup $ Kreturn f.(f_return) $ fun x => |={top}=>?u |> Q x)
    | Builtin builtin =>
      let ts := List.map snd f.(f_params) in
      wp_builtin_func builtin (Tfunction $ @FunctionType _ f.(f_cc) f.(f_arity) f.(f_return) ts) args Q
    end
  end.
mlock Definition wp_func `{Σ : cpp_logic, σ : genv} :=
  Cbn (Reduce (wp_func' true)).

Definition func_ok `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (f : Func) (spec : function_spec) : mpred :=
  [| type_of_spec spec = type_of_value (Ofunction f) |] **
  □ Forall (Q : ptr -> epred) vals,
  spec.(fs_spec) vals Q -* wp_func tu f vals Q.

Section wp_func.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (Q : ptr -> epred).

  Lemma wp_func_frame tu tu' f args Q Q' :
    sub_module tu tu' ->
    Forall p, Q p -* Q' p
    |-- wp_func tu f args Q -* wp_func tu' f args Q'.
  Proof.
    intros. rewrite wp_func.unlock. iIntros "HQ".
    case_match; last by auto.
    case_match; last by iApply wp_builtin_func_frame.
    all: iApply bind_vars_frame; [done|]; iIntros (??) "wp !>"; iRevert "wp".
    all: iApply wp_frame; [done|]; iIntros (?).
    all: iApply Kcleanup_frame; [done|].
    all: iApply Kreturn_frame; iIntros (?) "Q".
    all: iApply ("HQ" with "Q").
  Qed.

  (** Unsupported *)
  Lemma wp_func_shift tu f args Q :
    (|={top}=> wp_func tu f args (fun p => |={top}=> Q p))
    |-- wp_func tu f args Q.
  Abort.

  Lemma wp_func_intro tu f args Q :
    Cbn (Reduce (wp_func' false tu f args Q)) |-- wp_func tu f args Q.
  Proof.
    rewrite wp_func.unlock. repeat case_match; auto.
    iApply bind_vars_frame; [done|]. iIntros (??) "wp !>"; iRevert "wp".
    iApply wp_frame; [done|]. iIntros (?).
    iApply Kcleanup_frame; [done|].
    iApply Kreturn_frame. auto.
  Qed.

  Lemma wp_func_elim tu f args Q :
    wp_func tu f args Q |-- Cbn (Reduce (wp_func' true tu f args Q)).
  Proof. by rewrite wp_func.unlock. Qed.
End wp_func.

(** ** Defaulted copy and move operations of unions

A union's defaulted copy/move constructors and copy/move assignment
operators copy the object representation of the source into the
destination (C++23 [class.copy.ctor]/14 and [class.copy.assign]/13).
Clang's AST does not express this copy: it gives these members an empty
body (constructors) or <<return *this;>> (assignment operators) because
clang's code generator performs the copy at the call site. cpp2v
therefore prints them as [Defaulted], and [wp_union_copy] gives them
their meaning.

The state of a union object in this logic is [unionR] together with its
active member (if any). Copying the object representation of [src] into
[dst] makes [src]'s active member the active member of [dst] and copies
its bytes. The rule is stated with raw bytes ([rawsR]) because the active
member can have any trivially copyable type; [primR_to_rawsR] converts
primitive members to and from raw bytes.

[wp_union_copy cls un src dst Q] requires [src] to be a [cls] object with
active member [i] whose bytes are [rs] (any fraction), and gives [dst]
active member [i] with the same bytes (full ownership). The caller
supplies the memory of [dst] separately: the previous object for
assignment, or the object's block for construction.

Soundness. The prover chooses [i], [m], [q] and [rs], so each choice must
be harmless:
- [i] and [m] are fixed by [src]'s [unionR] and [u_fields].
- [rs] is exactly [size_of mty] bytes, all owned at [src ,, f]: a shorter
  list would copy only part of the member, and a longer one would give
  [dst] ownership of bytes past the copied object that the copy never
  transfers. The member sits at offset 0 and fits in the union, so these
  bytes lie inside [dst]'s object.
- No enclosing object can place another subobject in these bytes. A union
  that is a [[no_unique_address]] member lends only its tail padding past
  its data size, and the data size covers each member's [sizeof] unless
  that member is itself [[no_unique_address]]. cpp2v gives no body to the
  copy/move operations of unions with such members (it does not record
  data sizes), so this rule never applies to them.
- [dst] gets full ownership of these bytes and of [unionR], which the
  caller paid for with the whole of [dst]'s storage ([anyR] or [tblockR]
  at full fraction); [src] gets back exactly what it lent.
This rule needs separate ownership of [src] and [dst], which the full
[anyR] of [dst] rules out when they are the same object; self-assignment
is [wp_union_self_copy].
*)
Definition wp_union_copy `{Σ : cpp_logic, σ : genv} (cls : globname) (un : decl.Union)
    (src dst : ptr) (Q : mpred) : mpred :=
  Exists (i : nat) (m : Member) (q : cQp.t) (rs : list raw_byte),
    [| un.(u_fields) !! i = Some m |] **
    let f := o_field σ (Field cls m.(mem_name)) in
    let mty := erase_qualifiers m.(mem_type) in
    [| size_of σ mty = Some (lengthN rs) |] **
    src |-> unionR cls q (Some i) ** src ,, f |-> rawsR q rs **
    (src |-> unionR cls q (Some i) -* src ,, f |-> rawsR q rs -*
     dst |-> unionR cls 1$m (Some i) -* dst ,, f |-> (type_ptrR mty ** rawsR 1$m rs) -*
     Q).
#[global] Arguments wp_union_copy : simpl never.

Section wp_union_copy.
  Context `{Σ : cpp_logic, σ : genv}.

  Lemma wp_union_copy_frame cls un src dst Q Q' :
    (Q -* Q') |-- wp_union_copy cls un src dst Q -* wp_union_copy cls un src dst Q'.
  Proof.
    rewrite /wp_union_copy. iIntros "HQ wp".
    iDestruct "wp" as (i m q rs) "(% & % & S & F & wp)".
    iExists i, m, q, rs. iFrame "S F". do 2 (iSplit; first done).
    iIntros "? ? ? ?". iApply "HQ". iApply ("wp" with "[$] [$] [$] [$]").
  Qed.
End wp_union_copy.

(** Self-assignment of a union ([x = x], or [*p = *q] with [p = q]) copies
the object representation of [p] onto itself, so it changes nothing.

[wp_union_self_copy cls un p Q] requires full ownership of [p]'s object
representation, active member [i] with bytes [rs], and gives it back
unchanged.

Soundness. The prover chooses [i], [m] and [rs]:
- [i] and [m] are fixed by [p]'s [unionR] and [u_fields], and the resources
  are returned exactly as given, so no choice can change the active member
  or its bytes.
- Ownership is full ([1$m]), not just enough to read: the copy writes every
  byte of the object, and a concurrent read by a holder of another fraction
  would be a data race even though the written bytes are unchanged. So [rs]
  is exactly [size_of mty] bytes, as in [wp_union_copy], and [unionR] at
  full fraction covers the union's remaining bytes (its padding).
Only assignment uses this rule: a self copy-construction reads the
storage it is about to initialize.
*)
Definition wp_union_self_copy `{Σ : cpp_logic, σ : genv} (cls : globname) (un : decl.Union)
    (p : ptr) (Q : mpred) : mpred :=
  Exists (i : nat) (m : Member) (rs : list raw_byte),
    [| un.(u_fields) !! i = Some m |] **
    let f := o_field σ (Field cls m.(mem_name)) in
    let mty := erase_qualifiers m.(mem_type) in
    [| size_of σ mty = Some (lengthN rs) |] **
    p |-> unionR cls 1$m (Some i) ** p ,, f |-> rawsR 1$m rs **
    (p |-> unionR cls 1$m (Some i) -* p ,, f |-> rawsR 1$m rs -* Q).
#[global] Arguments wp_union_self_copy : simpl never.

Section wp_union_self_copy.
  Context `{Σ : cpp_logic, σ : genv}.

  Lemma wp_union_self_copy_frame cls un p Q Q' :
    (Q -* Q') |-- wp_union_self_copy cls un p Q -* wp_union_self_copy cls un p Q'.
  Proof.
    rewrite /wp_union_self_copy. iIntros "HQ wp".
    iDestruct "wp" as (i m rs) "(% & % & U & F & wp)".
    iExists i, m, rs. iFrame "U F". do 2 (iSplit; first done).
    iIntros "? ?". iApply "HQ". iApply ("wp" with "[$] [$]").
  Qed.
End wp_union_self_copy.

(** ** The weakest precondition of a method *)
(**
Note that in the calling convention for methods, the [this] parameter
is passed directly rather than being materialized like normal
parameters.
*)
#[local] Definition wp_method' `{Σ : cpp_logic, σ : genv} (u : bool) (tu : translation_unit)
    (m : Method) (args : list ptr) (Q : ptr -> epred) : mpred :=
  match m.(m_body) with
  | None => ERROR "wp_method: no body"
  | Some (UserDefined body | CompilerProvided body) =>
    match args with
    | thisp :: rest_vals =>
      let ρ va := Remp (Some thisp) va m.(m_return) in
      letI* ρ, cleanup := bind_vars tu m.(m_arity) m.(m_params) rest_vals ρ in
      |> wp tu ρ body (Kcleanup tu cleanup $ Kreturn m.(m_return) $ fun x => |={top}=>?u |> Q x)
    | _ => ERROR "wp_method: no arguments"
    end
  | Some Defaulted =>
    (* A union's defaulted copy or move assignment operator (see
       [wp_union_copy] and [wp_union_self_copy]). It returns a reference to
       the destination. *)
    match args, tu.(types) !! m.(m_class) with
    | [thisp; srcp], Some (Gunion un) =>
      let ty := Tnamed m.(m_class) in
      let K : mpred := (|={top}=>?u |> Forall p : ptr, p |-> primR (Tref ty) 1$m (Vref thisp) -* Q p)%I in
      (thisp |-> anyR ty 1$m **
       |>
       (* [srcp] is the (materialized) reference parameter; read it like
          [read_decl] does. *)
       (Exists src : ptr,
         ((Exists q, srcp |-> primR (Tref ty) q (Vref src) ** True) //\\
          wp_union_copy m.(m_class) un src thisp K))) \\//
      (* Self-assignment: [srcp] refers to [thisp] itself. *)
      |>
      ((Exists q, srcp |-> primR (Tref ty) q (Vref thisp) ** True) //\\
       wp_union_self_copy m.(m_class) un thisp K)
    | _, _ => UNSUPPORTED "wp_method: defaulted methods"
    end
  end.
mlock Definition wp_method `{Σ : cpp_logic, σ : genv} :=
  Cbn (Reduce (wp_method' true)).

Definition method_ok `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (m : Method) (spec : function_spec) : mpred :=
  [| type_of_spec spec = type_of_value (Omethod m) |] **
  □ Forall (Q : ptr -> mpred) vals,
  spec.(fs_spec) vals Q -* wp_method tu m vals Q.

Section wp_method.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (Q : ptr -> epred).

  Lemma wp_method_frame tu tu' m args Q Q' :
    sub_module tu tu' ->
    Forall p, Q p -* Q' p
    |-- wp_method tu m args Q -* wp_method tu' m args Q'.
  Proof.
    intros. iIntros "HQ". rewrite wp_method.unlock.
    destruct m as [m_return m_class m_this_qual m_params m_cc m_arity m_exception m_attrs m_body]; cbn.
    destruct m_body as [[|body|body]|]; auto.
    { destruct args as [|thisp [|srcp [|??]]]; auto.
      destruct (tu.(types) !! m_class) as [[|un| | | | | | |]|] eqn:Hun;
        try (iIntros "H"; iDestruct (UNSUPPORTED_elim with "H") as "[]").
      erewrite sub_module_preserves_gunion; [|done..].
      iIntros "[[A wp]|wp]".
      - iLeft. iFrame "A". iNext. iDestruct "wp" as (src) "wp". iExists src.
        iSplit; first by iDestruct "wp" as "[$ _]". iDestruct "wp" as "[_ wp]".
        iApply (wp_union_copy_frame with "[HQ] wp").
        iIntros ">wp !> !> %p R". iApply "HQ". by iApply "wp".
      - iRight. iNext.
        iSplit; first by iDestruct "wp" as "[$ _]". iDestruct "wp" as "[_ wp]".
        iApply (wp_union_self_copy_frame with "[HQ] wp").
        iIntros ">wp !> !> %p R". iApply "HQ". by iApply "wp". }
    all: destruct args as [|thisp rest_vals]; auto.
    all: iApply bind_vars_frame; [done|]; iIntros (??) "wp !>"; iRevert "wp".
    all: iApply wp_frame; [done|]; iIntros (?).
    all: iApply Kcleanup_frame; [done|].
    all: iApply Kreturn_frame; iIntros (?) "Q".
    all: iApply ("HQ" with "Q").
  Qed.

  (** Unsupported *)
  Lemma wp_method_shift tu m args Q :
    (|={top}=> wp_method tu m args (fun p => |={top}=> Q p))
    |-- wp_method tu m args Q.
  Abort.

  Lemma wp_method_intro tu m args Q :
    Cbn (Reduce (wp_method' false tu m args Q)) |-- wp_method tu m args Q.
  Proof.
    rewrite wp_method.unlock.
    destruct m as [m_return m_class m_this_qual m_params m_cc m_arity m_exception m_attrs m_body]; cbn.
    destruct m_body as [[|body|body]|]; auto.
    { destruct args as [|thisp [|srcp [|??]]]; auto.
      case_match; auto. case_match; auto.
      iIntros "[[A wp]|wp]".
      - iLeft. iFrame "A". iNext. iDestruct "wp" as (src) "wp". iExists src.
        iSplit; first by iDestruct "wp" as "[$ _]". iDestruct "wp" as "[_ wp]".
        iApply (wp_union_copy_frame with "[] wp").
        iIntros "wp !> !> %p R". by iApply "wp".
      - iRight. iNext.
        iSplit; first by iDestruct "wp" as "[$ _]". iDestruct "wp" as "[_ wp]".
        iApply (wp_union_self_copy_frame with "[] wp").
        iIntros "wp !> !> %p R". by iApply "wp". }
    all: destruct args as [|thisp rest_vals]; auto.
    all: iApply bind_vars_frame; [done|]; iIntros (??) "wp !>"; iRevert "wp".
    all: iApply wp_frame; [done|]; iIntros (?).
    all: iApply Kcleanup_frame; [done|].
    all: iApply Kreturn_frame; auto.
  Qed.

  Lemma wp_method_elim tu m args Q :
    wp_method tu m args Q |-- Cbn (Reduce (wp_method' true tu m args Q)).
  Proof. by rewrite wp_method.unlock. Qed.
End wp_method.

(** ** Weakest precondition of a constructor *)

(**
Initialization of members in the initializer list
*)
Definition wpi_members `{Σ : cpp_logic, σ : genv} (tu : translation_unit) (ρ : region)
    (cls : globname) (this : ptr) (inits : list Initializer) :=
  fix wpi_members (members : list Member) (Q : epred) : mpred :=
  match members with
  | nil => Q
  | m :: members =>
    let initializer_for (i : Initializer) :=
      match i.(init_path) with
      | InitField x
      | InitIndirect ((x,_) :: _) _ => bool_decide (m.(mem_name) = x)
      | _ => false
      end
    in
    match List.filter initializer_for inits with
    | nil =>
      (*
      there is no initializer for this member, so we "default
      initialize" it (see https://eel.is/c++draft/dcl.init#general-7 )
      *)
      let* frees :=
        default_initialize tu m.(mem_type)
          (this ,, _field (Field cls m.(mem_name)))
      in
      let* := interp tu frees in
      wpi_members members Q
    | i :: is' =>
      match i.(init_path) with
      | InitField _ (* = m.(mem_name) *) =>
        match is' with
        | nil =>
          (* there is a *unique* initializer for this field *)
          wpi tu ρ cls this m.(mem_type) i (wpi_members members Q)
        | _ =>
          (* there are multiple initializers for this field *)
          ERROR ("multiple initializers for field", (cls, m))
        end
      | InitIndirect _ _ =>
        (*
        this is initializing an object via sub-objets using indirect
        initialization.

        TODO currently not supported
        *)
        UNSUPPORTED ("indirect initialization", (cls, m))
      | _ => False%I (* unreachable due to the filter *)
      end
    end
  end.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (p : ptr) (Q : epred).

  Lemma wpi_members_frame tu tu' ρ cls this inits flds Q Q' :
    sub_module tu tu' ->
    Q -* Q'
    |-- wpi_members tu ρ cls this inits flds Q -* wpi_members tu' ρ cls this inits flds Q'.
  Proof.
    intros. move: Q Q'. induction flds; intros; first done. cbn.
    case_match.
    { iIntros "a"; iApply default_initialize_frame; [done|].
      iIntros (?); iApply interp_frame_strong; [done|]. by iApply IHflds. }
    { case_match; eauto.
      case_match; eauto.
      iIntros "a".
      iApply wpi_frame; [done|].
      by iApply IHflds. }
  Qed.
End with_cpp.

(**
Initialization of bases in the initializer list
*)
Definition wpi_bases `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (ρ : region) (cls : globname) (this : ptr) (inits : list Initializer) :=
  fix wpi_bases (bases : list globname) (Q : epred) : mpred :=
  match bases with
  | nil => Q
  | b :: bases =>
    match List.filter (fun i => bool_decide (i.(init_path) = InitBase b)) inits with
    | nil =>
      (*
      There is no initializer for this base class.
      *)
      ERROR ("wpi_bases: missing base class initializer: ", cls)
    | i :: nil =>
      (* there is an initializer for this class; once it returns, the base's
         identity is unsettled until [wp_init_identity] *)
      wpi tu ρ cls this (Tnamed b) i
        (wp_unsettle_identity (this ,, _base cls b) tu b (wpi_bases bases Q))
    | _ :: _ :: _ =>
      (* there are multiple initializers for this, so we fail *)
      ERROR ("wpi_bases: multiple initializers for base: ", cls, b)
    end
  end.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (p : ptr) (Q : epred).

  Lemma wpi_bases_frame tu tu' ρ cls p inits bases Q Q' :
    sub_module tu tu' ->
    Q -* Q'
    |-- wpi_bases tu ρ cls p inits bases Q -* wpi_bases tu' ρ cls p inits bases Q'.
  Proof.
    intros. move: Q Q'. induction bases; intros; first done.
    rewrite/wpi_bases-/(wpi_bases _ _ _ _ _).
    do 2!(case_match; auto). iIntros "?".
    iApply wpi_frame; [done|].
    iApply wp_unsettle_identity_frame; [done|].
    by iApply IHbases.
  Qed.
End with_cpp.

Definition wp_struct_initializer_list `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (s : Struct) (ρ : region) (cls : globname) (this : ptr)
    (inits : list Initializer) (Q : epred) : mpred :=
  match List.find (fun i => bool_decide (i.(init_path) = InitThis)) inits with
  | Some {| init_init := e |} =>
    match inits with
    | _ :: nil =>
        (* this is a delegating constructor, simply delegate. *)
        wp_init tu ρ (Tnamed cls) this e (fun frees => interp tu frees Q)
    | _ =>
      (*
      delegating constructors are not allowed to have any other
      initializers
      *)
      ERROR "wp_struct_initializer_list: delegating constructor has other initializers"
    end
  | None =>
    let bases := wpi_bases tu ρ cls this inits (List.map fst s.(s_bases)) in
    let members := wpi_members tu ρ cls this inits s.(s_fields) in
    let ident Q := wp_init_identity this tu cls Q in
    (**
    Provide strict validity for [this] and immediate members,
    initialize the bases, then the identity, then initialize the
    members, following http://eel.is/c++draft/class.base.init#13
    (except virtual base classes, which are unsupported)

    NOTE we get the [structR] at the end since [structR 1$m
    cls |-- type_ptrR (Tnamed cls)].
    *)
    this |-> svalid_members cls ((fun m => (m.(mem_name), m.(mem_type))) <$> s.(s_fields)) -*
    bases (ident (members (this |-> structR cls 1$m -* Q)))
  end.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (p : ptr) (Q : epred).

  Lemma wp_struct_initializer_list_frame tu s ρ cls p inits Q Q' :
    (**
    NOTE: We cannot presently weaken by [sub_module tu tu'] due to the
    embedded [wp_init_identity].
    *)
    Q -* Q'
    |-- wp_struct_initializer_list tu s ρ cls p inits Q -* wp_struct_initializer_list tu s ρ cls p inits Q'.
  Proof.
    rewrite /wp_struct_initializer_list. case_match.
    { repeat (case_match; auto). iIntros "?".
      iApply wp_init_frame; [done|]. iIntros (?).
      by iApply interp_frame_strong. }
    { iIntros "?".
      iApply wand_frame.
      iApply wpi_bases_frame; [done|].
      iApply wp_init_identity_frame => //.
      iApply wpi_members_frame; [done|].
      by iApply wand_frame. }
  Qed.
End with_cpp.

(** ** Constructing objects of classes with virtual bases

A class [C] with virtual bases (see [VStruct]) is constructed in two
steps (https://eel.is/c++draft/class.base.init#13):

1. _only_ when [C] is the most-derived class, its virtual bases are
   initialized, with the initializers of the constructor of [C];
2. then its non-virtual bases and its fields are initialized and the
   body of the constructor runs.

A constructor has one body and one specification, which describe step
2 only: [wp_ctor] takes the storage of the non-virtual part
([nv_tblockR]) and never initializes a virtual base. The
specification of such a constructor typically takes the [Rep]s of the
(already constructed) virtual bases as a pre-condition and returns
the full [Rep] of the class.

Step 1 belongs to whoever constructs a complete object:
[wp_init_complete_vstruct] below. Base-class subobjects are
constructed with [wp_base_ctor_call], which skips it.

The location of each virtual base is fixed by step 1, which
introduces the [vbase_ptr] facts of the complete object; initializing
a base-class subobject derives the facts of that subobject from those
of the class being constructed ([vbase_facts_down]).

We do not yet update object identities ([wp_init_identity]) across
virtual bases, so these rules only apply when no class in the
hierarchy has a virtual function ([no_vtables]); there is then no
identity to update.
*)

(**
[no_vtables tu fuel cls] holds if no class in the hierarchy of [cls]
(itself, its bases and its virtual bases, transitively) has a vtable.
*)
Fixpoint no_vtables (tu : translation_unit) (fuel : nat) (cls : globname) : bool :=
  match fuel with
  | 0 => false
  | S fuel =>
    match tu.(types) !! cls with
    | Some (Gstruct st) =>
      negb (has_vtable st) &&
      forallb (fun b => no_vtables tu fuel b.1) st.(s_bases)
    | Some (Gvstruct vs) =>
      negb (has_vtable vs.(vs_struct)) &&
      forallb (fun b => no_vtables tu fuel b.1) vs.(vs_struct).(s_bases) &&
      forallb (fun b => no_vtables tu fuel b.1) vs.(vs_vbases)
    | _ => false
    end
  end.

(** The hierarchy of [cls] has no vtable (the number of global entries
bounds its height, as in [derivationsR]). *)
Definition tu_no_vtables (tu : translation_unit) (cls : globname) : bool :=
  no_vtables tu (NM.cardinal tu.(types)) cls.

(**
Layout metadata is untrusted (see [valid_alignment]), and the rules
below hand out storage according to it, so they check it first: a
rule that handed out contradictory storage would be vacuous.

[vstruct_nv_ok vs] validates the non-virtual part: its alignment is a
power of two that divides the alignment of a complete object, and it
is not larger than a complete object.
*)
Definition vstruct_nv_ok (vs : VStruct) : bool :=
  bool_decide (valid_alignment vs.(vs_struct).(s_alignment) vs.(vs_nv_alignment)) &&
  bool_decide (vs.(vs_nv_size) <= vs.(vs_struct).(s_size))%N.

(** The storage that a virtual base [b] occupies: all of it for an
ordinary class, only the non-virtual part for a class that has
virtual bases itself. *)
Definition vbase_extent (tu : translation_unit) (b : globname) : option Z :=
  match tu.(types) !! b with
  | Some (Gstruct s) => Some (Z.of_N s.(s_size))
  | Some (Gvstruct vs) => Some (Z.of_N vs.(vs_nv_size))
  | _ => None
  end.

Fixpoint extents_disjoint (xs : list (Z * Z)) : bool :=
  match xs with
  | nil => true
  | x :: xs =>
    forallb (fun y => bool_decide (x.1 + x.2 <= y.1)%Z || bool_decide (y.1 + y.2 <= x.1)%Z) xs &&
    extents_disjoint xs
  end.

(**
[vstruct_layout_ok tu vs] validates the layout of a complete object:
the non-virtual part is valid, the virtual bases are distinct, and
their storage lies after the non-virtual part, inside the object,
without overlap. An implementation may overlap virtual bases (e.g.
an empty one, or one placed in the tail padding of another); complete
objects of such classes are not supported.
*)
Definition vstruct_layout_ok (tu : translation_unit) (vs : VStruct) : bool :=
  vstruct_nv_ok vs &&
  bool_decide (NoDup (List.map fst vs.(vs_vbases))) &&
  match
    mapM (fun b => (fun e => (b.2.(li_offset) / 8, e)%Z) <$> vbase_extent tu b.1) vs.(vs_vbases)
  with
  | Some exts =>
    forallb (fun x =>
      bool_decide (Z.of_N vs.(vs_nv_size) <= x.1)%Z &&
      bool_decide (x.1 + x.2 <= Z.of_N vs.(vs_struct).(s_size))%Z) exts &&
    extents_disjoint exts
  | None => false
  end.

(**
[ctor_fun_type tu cnd cls] is the type of the constructor [cnd] of
class [cls], with the types of its arguments (without [this]).
*)
Definition ctor_fun_type (tu : translation_unit) (cnd : obj_name) (cls : globname)
    : option (functype * (list decltype * function_arity)) :=
  match tu.(symbols) !! cnd with
  | Some (Oconstructor ctor as v) =>
    if bool_decide (ctor.(c_class) = cls) then
      let ty := type_of_value v in
      match ty with
      | Tfunction {| ft_arity := ar ; ft_params := _ :: args |} => Some (ty, (args, ar))
      | _ => None
      end
    else None
  | _ => None
  end.

(**
[wp_base_ctor_call tu ρ cls this e Q] runs the constructor call [e]
on the non-virtual part of an object of class [cls] (with virtual
bases) at [this]. Compare [wp_init_constructor] in [expr.v].
*)
Definition wp_base_ctor_call `{Σ : cpp_logic, σ : genv} (tu : translation_unit) (ρ : region)
    (cls : globname) (this : ptr) :=
  fix wp_base_ctor_call (e : Expr) (Q : FreeTemps -> epred) : mpred :=
  match e with
  | Econstructor cnd es _ =>
    match ctor_fun_type tu cnd cls , glob_def σ cls with
    | Some (ctor_type, arg_types) , Some (Gvstruct vs) =>
      if vstruct_nv_ok vs then
        (letI* _, argps, ifree, free := wp_args tu ρ evaluation_order.nd nil arg_types es in
        |> (this |-> nv_tblockR cls 1$m -*
            letI* resultp := wp_fptr ctor_type (_global cnd) (this :: argps) in
            letI* := interp tu ifree in
            (* in the semantics, constructors return [void] *)
            resultp |-> primR Tvoid 1$m Vvoid **
            Q free))%I
      else ERROR ("wp_base_ctor_call: invalid layout", cls)
    | _ , _ => ERROR ("wp_base_ctor_call: constructor not found", cnd)
    end
  | Eandclean e =>
    (* as [wp_init_clean] *)
    wp_base_ctor_call e (fun frees => interp tu frees $ Q FreeTemps.id)
  | _ => UNSUPPORTED ("wp_base_ctor_call: initializer for a class with virtual bases", e)
  end.

(**
[vbase_facts_down cls base this vbases Q] derives the locations of the
virtual bases [vbases] of the [base] subobject of the object of class
[cls] at [this] from those of [cls]: they are the same.
*)
Definition vbase_facts_down `{Σ : cpp_logic, σ : genv} (cls base : globname) (this : ptr) :=
  fix vbase_facts_down (vbases : list globname) (Q : mpred) : mpred :=
  match vbases with
  | nil => Q
  | vb :: vbases =>
    Exists pvb, vbase_ptr cls vb this pvb **
    (vbase_ptr base vb (this ,, _base cls base) pvb -* vbase_facts_down vbases Q)
  end.

(**
Initialization of the direct non-virtual bases of a class with virtual
bases, in the initializer list. A base that has virtual bases itself
is initialized as a base-class subobject.
*)
Definition wpi_nv_bases `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (ρ : region) (cls : globname) (this : ptr) (inits : list Initializer) :=
  fix wpi_nv_bases (bases : list globname) (Q : epred) : mpred :=
  match bases with
  | nil => Q
  | b :: bases =>
    match List.filter (fun i => bool_decide (i.(init_path) = InitBase b)) inits with
    | nil =>
      ERROR ("wpi_nv_bases: missing base class initializer: ", cls)
    | i :: nil =>
      match tu.(types) !! b with
      | Some (Gstruct _) =>
        wpi tu ρ cls this (Tnamed b) i (wpi_nv_bases bases Q)
      | Some (Gvstruct bvs) =>
        let pb := this ,, _base cls b in
        (letI* := vbase_facts_down cls b this (List.map fst bvs.(vs_vbases)) in
         letI* free := wp_base_ctor_call tu ρ b pb i.(init_init) in
         letI* := interp tu free in
         wpi_nv_bases bases Q)%I
      | _ => ERROR ("wpi_nv_bases: base is not a class: ", cls, b)
      end
    | _ :: _ :: _ =>
      ERROR ("wpi_nv_bases: multiple initializers for base: ", cls, b)
    end
  end.

Definition wp_vstruct_initializer_list `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (vs : VStruct) (ρ : region) (cls : globname) (this : ptr)
    (inits : list Initializer) (Q : epred) : mpred :=
  if tu_no_vtables tu cls then
    match List.find (fun i => bool_decide (i.(init_path) = InitThis)) inits with
    | Some {| init_init := e |} =>
      match inits with
      | _ :: nil =>
        (* this is a delegating constructor: the target constructs the
           non-virtual part, too. *)
        wp_base_ctor_call tu ρ cls this e (fun frees => interp tu frees Q)
      | _ =>
        ERROR "wp_vstruct_initializer_list: delegating constructor has other initializers"
      end
    | None =>
      let s := vs.(vs_struct) in
      (**
      Provide strict validity for the members, initialize the
      non-virtual bases, then the members. The initializers for
      virtual bases are not run here.
      *)
      this |-> svalid_members cls ((fun m => (m.(mem_name), m.(mem_type))) <$> s.(s_fields)) -*
      wpi_nv_bases tu ρ cls this inits (List.map fst s.(s_bases))
        (wpi_members tu ρ cls this inits s.(s_fields) Q)
    end
  else
    UNSUPPORTED ("constructor of a class with virtual bases and virtual functions", cls).

(**
[vbase_facts tu cls this vps] are the locations of the virtual bases
of a _complete_ object of class [cls] at [this]; [vps] pairs each
virtual base with its location. A virtual base that has virtual bases
of its own finds them at the same locations.
*)
Definition vbase_facts `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (cls : globname) (this : ptr) (vps : list (globname * ptr)) : mpred :=
  [** list] vp ∈ vps,
    vbase_ptr cls vp.1 this vp.2 **
    match tu.(types) !! vp.1 with
    | Some (Gvstruct vvs) =>
      [** list] w ∈ vvs.(vs_vbases),
        match List.find (fun wp => bool_decide (wp.1 = w.1)) vps with
        | Some wp => vbase_ptr vp.1 w.1 vp.2 wp.2
        | None => emp
        end
    | _ => emp
    end.

(**
Initialization of the virtual bases [vps] of a complete object, with
the initializers [inits] of its constructor.
*)
Definition wpi_vbases `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (ρ : region) (cls : globname) (inits : list Initializer) :=
  fix wpi_vbases (vps : list (globname * ptr)) (Q : epred) : mpred :=
  match vps with
  | nil => Q
  | vp :: vps =>
    match List.filter (fun i => bool_decide (i.(init_path) = InitBase vp.1)) inits with
    | nil =>
      ERROR ("wpi_vbases: missing virtual base class initializer: ", cls, vp.1)
    | i :: nil =>
      match tu.(types) !! vp.1 with
      | Some (Gstruct _) =>
        (letI* free := wp_initialize tu ρ (Tnamed vp.1) vp.2 i.(init_init) in
         letI* := interp tu free in
         wpi_vbases vps Q)%I
      | Some (Gvstruct _) =>
        (letI* free := wp_base_ctor_call tu ρ vp.1 vp.2 i.(init_init) in
         letI* := interp tu free in
         wpi_vbases vps Q)%I
      | _ => ERROR ("wpi_vbases: virtual base is not a class: ", cls, vp.1)
      end
    | _ :: _ :: _ =>
      ERROR ("wpi_vbases: multiple initializers for virtual base: ", cls, vp.1)
    end
  end.

(**
[wp_init_complete_vstruct tu ρ cls vs cv this cnd es Q] constructs a
_complete_ object of class [cls] (with virtual bases) at [this], by
calling the constructor [cnd] on the arguments [es].

After evaluating the arguments, the abstract machine picks the
locations [pvbs] of the virtual bases, initializes each of them with
the initializer that the constructor [cnd] has for it, and only then
calls [cnd], which constructs the non-virtual part.

The initializers of the virtual bases belong to [cnd], so this rule
needs its definition: it does not apply to a constructor that is only
declared in [tu]. They are evaluated in the environment of [cnd],
i.e. with its parameters bound to the arguments exactly as [wp_ctor]
binds them (<<const>> parameters are <<const>>); the parameters are
then released so that [cnd] can bind them again.

NOTE: a delegating constructor leaves the virtual bases to its target
(whose arguments it evaluates first); this is not supported yet.
*)
Definition wp_init_complete_vstruct `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (ρ : region) (cls : globname) (vs : VStruct) (cv : type_qualifiers) (this : ptr)
    (cnd : obj_name) (es : list Expr) (Q : FreeTemps -> epred) : mpred :=
  match tu.(symbols) !! cnd , ctor_fun_type tu cnd cls with
  | Some (Oconstructor ctor) , Some (ctor_type, arg_types) =>
    match ctor.(c_body) with
    | Some (UserDefined ib | CompilerProvided ib) =>
      let inits := ib.1 in
      if negb (vstruct_layout_ok tu vs) then
        UNSUPPORTED ("complete object with virtual bases: unsupported layout", cls)
      else if existsb (fun i => bool_decide (i.(init_path) = InitThis)) inits then
        UNSUPPORTED ("delegating constructor for a complete object with virtual bases", cnd)
      else
        (letI* _, argps, ifree, free := wp_args tu ρ evaluation_order.nd nil arg_types es in
        |> Forall pvbs : list ptr,
        [| length pvbs = length vs.(vs_vbases) |] -*
        let vps := zip (List.map fst vs.(vs_vbases)) pvbs in
        vbase_facts tu cls this vps -*
        let ρ' vap := Remp (Some this) vap Tvoid in
        letI* ρ', consts := bind_vars tu ctor.(c_arity) ctor.(c_params) argps ρ' in
        letI* := wpi_vbases tu ρ' cls inits vps in
        letI* := wp_make_mutables tu consts in
        this |-> nv_tblockR cls 1$m -*
        letI* resultp := wp_fptr ctor_type (_global cnd) (this :: argps) in
        letI* := interp tu ifree in
        (* in the semantics, constructors return [void] *)
        resultp |-> primR Tvoid 1$m Vvoid **
        let Q := Q free in
        if q_const cv
        then wp_make_const tu this (Tnamed cls) Q
        else Q)%I
    | _ =>
      UNSUPPORTED ("complete object with virtual bases: its constructor has no body here", cnd)
    end
  | _ , _ => ERROR ("Constructor not found.", cnd)
  end.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (p : ptr) (Q : epred).

  Lemma wp_base_ctor_call_frame tu ρ cls this e (Q Q' : FreeTemps -> epred) :
    (Forall free, Q free -* Q' free)
    |-- wp_base_ctor_call tu ρ cls this e Q -* wp_base_ctor_call tu ρ cls this e Q'.
  Proof.
    move: Q Q'. induction e => Q Q'; cbn; try by iIntros "_ $".
    - case_match; last by iIntros "_ $". case_match.
      destruct (glob_def σ cls) as [[]|]; try by iIntros "_ $".
      case_match; last by iIntros "_ $".
      iIntros "HQ". iApply (wp_args_frame with "[] [HQ]"); first done.
      iIntros (????) "wp !> B". iSpecialize ("wp" with "B"). iRevert "wp".
      iApply wp_fptr_frame. iIntros (?). iApply interp_frame.
      iIntros "[$ Q]". by iApply "HQ".
    - iIntros "HQ". iApply IHe. iIntros (?). iApply interp_frame. iApply "HQ".
  Qed.

  Lemma vbase_facts_down_frame cls base this vbases (Q Q' : mpred) :
    Q -* Q'
    |-- vbase_facts_down cls base this vbases Q -* vbase_facts_down cls base this vbases Q'.
  Proof.
    elim: vbases => [|vb vbases IH] /=; first by iIntros "$".
    iIntros "HQ (%pvb & $ & wp) V". iApply (IH with "HQ"). by iApply "wp".
  Qed.

  Lemma wpi_nv_bases_frame tu ρ cls p inits bases Q Q' :
    Q -* Q'
    |-- wpi_nv_bases tu ρ cls p inits bases Q -* wpi_nv_bases tu ρ cls p inits bases Q'.
  Proof.
    move: Q Q'. induction bases; intros; first by iIntros "$".
    rewrite /wpi_nv_bases-/(wpi_nv_bases _ _ _ _ _).
    destruct (List.filter _ _) as [|i [|??]]; [by iIntros "_ $"| |by iIntros "_ $"].
    destruct (_ !! _) as [[]|]; try by iIntros "_ $".
    - iIntros "HQ". iApply wpi_frame; [done|]. by iApply IHbases.
    - iIntros "HQ". iApply vbase_facts_down_frame.
      iApply wp_base_ctor_call_frame. iIntros (?).
      iApply interp_frame. by iApply IHbases.
  Qed.

  Lemma wp_vstruct_initializer_list_frame tu vs ρ cls p inits Q Q' :
    Q -* Q'
    |-- wp_vstruct_initializer_list tu vs ρ cls p inits Q -*
        wp_vstruct_initializer_list tu vs ρ cls p inits Q'.
  Proof.
    rewrite /wp_vstruct_initializer_list. case_match; last by iIntros "_ $".
    case_match.
    { repeat (case_match; try by iIntros "_ $"). iIntros "HQ".
      iApply wp_base_ctor_call_frame. iIntros (?). by iApply interp_frame. }
    { iIntros "HQ". iApply wand_frame.
      iApply wpi_nv_bases_frame.
      by iApply wpi_members_frame. }
  Qed.

  Lemma wpi_vbases_frame tu ρ cls inits vps Q Q' :
    Q -* Q'
    |-- wpi_vbases tu ρ cls inits vps Q -* wpi_vbases tu ρ cls inits vps Q'.
  Proof.
    move: Q Q'. induction vps; intros; first by iIntros "$".
    rewrite /wpi_vbases-/(wpi_vbases _ _ _ _).
    destruct (List.filter _ _) as [|i [|??]]; [by iIntros "_ $"| |by iIntros "_ $"].
    destruct (_ !! _) as [[]|]; try by iIntros "_ $".
    - iIntros "HQ". iApply wp_initialize_frame; [done|]. iIntros (?).
      iApply interp_frame. by iApply IHvps.
    - iIntros "HQ". iApply wp_base_ctor_call_frame. iIntros (?).
      iApply interp_frame. by iApply IHvps.
  Qed.
End with_cpp.

Definition wp_union_initializer_list `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (u : decl.Union) (ρ : region) (cls : globname) (this : ptr)
    (inits : list Initializer) (Q : epred) : mpred :=
  match inits with
  | [] => Q
  | [{| init_path := InitField f ; init_init := e |} as init] =>
    match list_find (fun m => f = m.(mem_name)) u.(u_fields) with
    | None => ERROR "wp_union_initializer_list: field not found"
    | Some (n, m) => wpi tu ρ cls this m.(mem_type) init $ this |-> unionR cls 1$m (Some n) -* Q
    end
  | _ =>
    UNSUPPORTED "wp_union_initializer_list: indirect (or self) union initialization is not currently supported"
  end.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (p : ptr) (Q : epred).

  Lemma wp_union_initializer_list_frame tu tu' u ρ cls p inits Q Q' :
    sub_module tu tu' ->
    Q -* Q'
    |-- wp_union_initializer_list tu u ρ cls p inits Q -* wp_union_initializer_list tu' u ρ cls p inits Q'.
  Proof.
    intros. rewrite/wp_union_initializer_list.
    repeat case_match; auto. iIntros "?".
    iApply wpi_frame; [done|].
    by iApply wand_frame.
  Qed.
End with_cpp.

(**
A special version of return to match the C++ rule that constructors
and destructors must not syntactically return a value, e.g. `return
f()` for `void f()` are not allowed.

NOTE: we could drop this in favor of relying on the compiler to check
this.
*)
Definition Kreturn_void_inner `{Σ : cpp_logic} (P : epred) (rt : ReturnType) : mpred :=
  match rt with
  | Normal | ReturnVoid => P
  | Break | Continue | ReturnVal _ | ReturnNRVO _ _ | Goto _ => False
  end.
#[global] Arguments Kreturn_void_inner _ _ _ _ !rt /.

Definition Kreturn_void `{Σ : cpp_logic} (P : epred) : Kpred :=
  KP $ Kreturn_void_inner P.
#[global] Hint Opaque Kreturn_void : typeclass_instances.

Section Kreturn_void.
  Context `{Σ : cpp_logic}.
  Implicit Types (Q : epred) (rt : ReturnType).

  Lemma Kreturn_void_frame Q Q' rt :
    Q -* Q' |-- Kreturn_void Q rt -* Kreturn_void Q' rt.
  Proof. destruct rt; auto. Qed.

  Lemma Kreturn_void_fupd Q :
    Kreturn_void (|={top}=> Q) |-- |={top}=> Kreturn_void Q.
  Proof.
    constructor=>rt /=. rewrite monPred_at_fupd /Kreturn_void_inner.
    by case_match; auto using bi.False_elim.
  Qed.
End Kreturn_void.

(**
[wp_ctor tu ctor args Q] is the weakest pre-condition (with
post-condition [Q]) running the constructor [ctor] with arguments
[args].

Note that the constructor semantics consumes the entire [blockR] of
the object that is being constructed and the C++ abstract machine
breaks this block down producing usable† memory.

**Alternative**: Because constructor calls are *always* syntactically
distinguished (since C++ does not allow taking a pointer to a
constructor), we know that any invocation of a constructor will be
from a [wp_init] which means that the C++ abstract machine will
already own the memory (see the documentation for [wp_init] in
[wp.v]). In order to enforce this semantically within the abstract
machine, we would need a new predicate to say "a constructor with the
given specification" (rather than simply desugaring this to "a
function with the given specification").

NOTE: supporting virtual inheritence will require us to add
constructor kinds here

† It is not necessarily initialized, e.g. because primitive fields are
not initialized (you get an [uninitR]), but you will get something
that implies [type_ptr].
*)
#[local] Definition wp_ctor' `{Σ : cpp_logic, σ : genv} (u : bool) (tu : translation_unit)
    (ctor : Ctor) (args : list ptr) (Q : ptr -> epred) : mpred :=
  match ctor.(c_body) with
  | None => ERROR "wp_ctor: no body"
  | Some Defaulted =>
    (* A union's defaulted copy or move constructor (see [wp_union_copy]).
       Like every constructor, it requires the *entire* block of memory
       [tblockR] that the object will use. *)
    match args, tu.(types) !! ctor.(c_class) with
    | [thisp; srcp], Some (Gunion un) =>
      let ty := Tnamed ctor.(c_class) in
      thisp |-> tblockR ty 1$m **
      |>
      (* [srcp] is the (materialized) reference parameter; read it like
         [read_decl] does. *)
      (Exists src : ptr,
        ((Exists q, srcp |-> primR (Tref ty) q (Vref src) ** True) //\\
         wp_union_copy ctor.(c_class) un src thisp
           (|={top}=>?u |> Forall p : ptr, p |-> primR Tvoid 1$m Vvoid -* Q p)))
    | _, _ => UNSUPPORTED "wp_ctor: defaulted constructors"
    end
  | Some (UserDefined ib | CompilerProvided ib) =>
    let inits := ib.1 in
    let body := ib.2 in
    match args with
    | thisp :: rest_vals =>
      let ty := Tnamed ctor.(c_class) in
      match tu.(types) !! ctor.(c_class) with
      | Some (Gstruct cls) =>
        (*
        this is a structure.

        We require that you give up the *entire* block of memory
        [tblockR] that the object will use.
        *)
        thisp |-> tblockR ty 1$m **
        |>
        let ρ vap := Remp (Some thisp) vap Tvoid in
        letI* ρ, cleanup := bind_vars tu ctor.(c_arity) ctor.(c_params) rest_vals ρ in
        letI* := wp_struct_initializer_list tu cls ρ ctor.(c_class) thisp inits in
        letI* := wp tu ρ body in
        letI* := Kcleanup tu cleanup in
        letI* := Kreturn_void in
        |={top}=>?u |> Forall p : ptr, p |-> primR Tvoid 1$m Vvoid -* Q p

      | Some (Gunion union) =>
        (*
        this is a union.

        We require that you give up the *entire* block of memory
        [tblockR] that the object will use.
        *)
        thisp |-> tblockR ty 1$m **
        |>
        let ρ vap := Remp (Some thisp) vap Tvoid in
        letI* ρ, cleanup := bind_vars tu ctor.(c_arity) ctor.(c_params) rest_vals ρ in
        letI* := wp_union_initializer_list tu union ρ ctor.(c_class) thisp inits in
        letI* := wp tu ρ body in
        letI* := Kcleanup tu cleanup in
        letI* := Kreturn_void in
        |={top}=>?u |> Forall p : ptr, p |-> primR Tvoid 1$m Vvoid -* Q p

      | Some (Gvstruct vs) =>
        (*
        this is a structure with virtual bases.

        The constructor only constructs the non-virtual part of the
        object, so it only takes the block of memory [nv_tblockR] of
        that part. The virtual bases are constructed beforehand by
        whoever constructs the complete object (see
        [wp_init_complete_vstruct]).
        *)
        thisp |-> nv_tblockR ctor.(c_class) 1$m **
        |>
        let ρ vap := Remp (Some thisp) vap Tvoid in
        letI* ρ, cleanup := bind_vars tu ctor.(c_arity) ctor.(c_params) rest_vals ρ in
        letI* := wp_vstruct_initializer_list tu vs ρ ctor.(c_class) thisp inits in
        letI* := wp tu ρ body in
        letI* := Kcleanup tu cleanup in
        letI* := Kreturn_void in
        |={top}=>?u |> Forall p : ptr, p |-> primR Tvoid 1$m Vvoid -* Q p

      (* This includes [Gopaque]: a constructor initializes the members and
         bases, which an opaque record does not describe. Constructors of
         opaque records can be specified and called, but not verified. *)
      | _ => ERROR ("wp_ctor: constructor for non-aggregate", ctor.(c_class))
      end
    | _ => ERROR "wp_ctor: constructor without leading [this] argument"
    end
  end.
mlock Definition wp_ctor `{Σ : cpp_logic, σ : genv} :=
  Cbn (Reduce (wp_ctor' true)).

Definition ctor_ok `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (ctor : Ctor) (spec : function_spec) : mpred :=
  [| type_of_spec spec = type_of_value (Oconstructor ctor) |] **
  □ Forall (Q : ptr -> epred) vals,
  spec.(fs_spec) vals Q -* wp_ctor tu ctor vals Q.

Section wp_ctor.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (Q : ptr -> epred).

  #[local] Ltac initializer_list_frame :=
    lazymatch goal with
    | |- context [wp_struct_initializer_list] => iApply wp_struct_initializer_list_frame
    | |- context [wp_vstruct_initializer_list] => iApply wp_vstruct_initializer_list_frame
    | |- context [wp_union_initializer_list] => iApply wp_union_initializer_list_frame; [done|]
    end.

  Lemma wp_ctor_frame tu c args Q Q' :
    (**
    NOTE: We cannot presently weaken by [sub_module tu tu'] due to the
    embedded [wp_init_identity].
    *)
    Forall p, Q p -* Q' p
    |-- wp_ctor tu c args Q -* wp_ctor tu c args Q'.
  Proof.
    iIntros "HQ". rewrite wp_ctor.unlock.
    destruct c as [c_class c_params c_cc c_arity c_exception c_body]; cbn.
    destruct c_body as [[|[inits body]|[inits body]]|]; auto.
    { destruct args as [|thisp [|srcp [|??]]]; auto.
      case_match; auto. case_match; auto.
      iIntros "[$ wp] !>". iDestruct "wp" as (src) "wp". iExists src.
      iSplit; first by iDestruct "wp" as "[$ _]". iDestruct "wp" as "[_ wp]".
      iApply (wp_union_copy_frame with "[HQ] wp").
      iIntros ">wp !> !> %p R". iApply "HQ". by iApply "wp". }
    all: repeat case_match; auto.
    all: iIntros "($ & wp) !>"; iRevert "wp".
    all: iApply bind_vars_frame; [done|]; iIntros (??).
    all: initializer_list_frame.
    all: iApply wp_frame; [done|]; iIntros (?).
    all: iApply Kcleanup_frame; [done|].
    all: iApply Kreturn_void_frame; iIntros ">HR !> !> % ?".
    all: iApply "HQ".
    all: by iApply "HR".
  Qed.

  (** Unsupported *)
  Lemma wp_ctor_shift tu c args Q :
    (|={top}=> wp_ctor tu c args (fun p => |={top}=> Q p))
    |-- wp_ctor tu c args Q.
  Abort.

  Lemma wp_ctor_intro tu c args Q :
    Cbn (Reduce (wp_ctor' false tu c args Q)) |-- wp_ctor tu c args Q.
  Proof.
    rewrite wp_ctor.unlock.
    destruct c as [c_class c_params c_cc c_arity c_exception c_body]; cbn.
    destruct c_body as [[|[inits body]|[inits body]]|]; auto.
    { destruct args as [|thisp [|srcp [|??]]]; auto.
      case_match; auto. case_match; auto.
      iIntros "[$ wp] !>". iDestruct "wp" as (src) "wp". iExists src.
      iSplit; first by iDestruct "wp" as "[$ _]". iDestruct "wp" as "[_ wp]".
      iApply (wp_union_copy_frame with "[] wp").
      iIntros "wp !> !> %p R". by iApply "wp". }
    all: repeat case_match; auto.
    all: iIntros "($ & wp) !>"; iRevert "wp".
    all: iApply bind_vars_frame; [done|]; iIntros (??).
    all: initializer_list_frame.
    all: iApply wp_frame; [done|]; iIntros (?).
    all: iApply Kcleanup_frame; [done|].
    all: iApply Kreturn_void_frame; iIntros "HQ !> !> % ?".
    all: by iApply "HQ".
  Qed.

  Lemma wp_ctor_elim tu c args Q :
    wp_ctor tu c args Q |-- Cbn (Reduce (wp_ctor' true tu c args Q)).
  Proof. by rewrite wp_ctor.unlock. Qed.
End wp_ctor.

(** ** Weakest precondition of a destructor *)

(**
[wpd_base tu cls this b Q] destroys the base subobject [this ,, _base cls b]:
it settles that base's identity with [b] as most-derived class, which [b]'s
destructor expects, and only then destroys it.
*)
Definition wpd_base `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (cls : globname) (this : ptr) (b : globname) (Q : epred) : mpred :=
  let base := this ,, _base cls b in
  wp_settle_identity base tu b (interp tu (FreeTemps.delete None (Tnamed b) base) Q).

(** [wpd_bases tu cls this bases Q] destroys the [bases] in reverse order. *)
Definition wpd_bases `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (cls : globname) (this : ptr) : list globname -> epred -> mpred :=
  fix wpd_bases (bases : list globname) (Q : epred) : mpred :=
  match bases with
  | nil => Q
  | b :: bases => wpd_bases bases (wpd_base tu cls this b Q)
  end.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (Q : epred).

  Lemma wpd_base_frame tu tu' cls this b Q Q' :
    sub_module tu tu' ->
    Q -* Q' |-- wpd_base tu cls this b Q -* wpd_base tu' cls this b Q'.
  Proof.
    intros. rewrite /wpd_base. iIntros "HQ".
    iApply wp_settle_identity_frame; [done|].
    by iApply interp_frame_strong.
  Qed.

  Lemma wpd_bases_frame tu tu' cls this bases Q Q' :
    sub_module tu tu' ->
    Q -* Q' |-- wpd_bases tu cls this bases Q -* wpd_bases tu' cls this bases Q'.
  Proof.
    intros. move: Q Q'. induction bases as [|b bases IH]; intros; cbn.
    { by iIntros "HQ". }
    iIntros "HQ". iApply IH. by iApply wpd_base_frame.
  Qed.
End with_cpp.

Definition wpd_members `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (cls : globname) (this : ptr) (members : list Member) (Q : epred) : mpred :=
  let del_member m := FreeTemps.delete None m.(mem_type) (this ,, _field (Field cls m.(mem_name))) in
  interp tu (FreeTemps.seqs_rev (List.map del_member members)) Q.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (Q : epred).

  Lemma wpd_members_frame tu tu' cls this members Q Q' :
    sub_module tu tu' ->
    Q -* Q' |-- wpd_members tu cls this members Q -* wpd_members tu' cls this members Q'.
  Proof. apply interp_frame_strong. Qed.
End with_cpp.

(**
Destruction of the direct non-virtual bases [bases] (in list order)
of a class with virtual bases. A base that has virtual bases itself is
destroyed as a base-class subobject ([wp_base_destructor]): its
virtual bases belong to the most-derived object. As in
[wpi_nv_bases], such a base finds its virtual bases where the class
being destroyed does ([vbase_facts_down]).
*)
Definition wpd_nv_bases `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (cls : globname) (this : ptr) :=
  fix wpd_nv_bases (bases : list globname) (Q : epred) : mpred :=
  match bases with
  | nil => Q
  | b :: bases =>
    match tu.(types) !! b with
    | Some (Gstruct _) =>
      interp tu (FreeTemps.delete None (Tnamed b) (this ,, _base cls b)) (wpd_nv_bases bases Q)
    | Some (Gvstruct bvs) =>
      vbase_facts_down cls b this (List.map fst bvs.(vs_vbases))
        (wp_base_destructor b (_global bvs.(vs_struct).(s_dtor)) (this ,, _base cls b)
           (wpd_nv_bases bases Q))
    | _ => ERROR ("wpd_nv_bases: base is not a class: ", cls, b)
    end
  end.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (Q : epred).

  Lemma wpd_nv_bases_frame tu cls this bases Q Q' :
    Q -* Q' |-- wpd_nv_bases tu cls this bases Q -* wpd_nv_bases tu cls this bases Q'.
  Proof.
    elim: bases => [|b bases IH] /=; first by iIntros "$".
    destruct (_ !! _) as [[]|]; try by iIntros "_ $".
    - iIntros "HQ". iApply interp_frame. by iApply IH.
    - iIntros "HQ". iApply vbase_facts_down_frame.
      iApply wp_base_destructor_frame. by iApply IH.
  Qed.
End with_cpp.

(**
[wp_dtor tu dtor args Q] defines the semantics of the destructor
[dtor] when applied to [args] with post-condition [Q].

Note that destructors are not always syntactically distinguished from
function calls (e.g. in the case of [c.~C()]). Therefore, in order to
have a uniform specification, they need to return the underlying
memory (i.e. a [this |-> tblockR (Tnamed cls) 1]) to the caller. When
the program is destroying this object, e.g. due to stack allocation,
this resource will be consumed immediately.
*)
#[local] Definition wp_dtor' `{Σ : cpp_logic, σ : genv} (upd : bool) (tu : translation_unit)
    (dtor : Dtor) (args : list ptr) (Q : ptr -> epred) : mpred :=
  match dtor.(d_body) with
  | None => ERROR "wp_dtor: no body"
  | Some body =>
    match args with
    | thisp :: nil =>
      let ty := Tnamed dtor.(d_class) in
      let wp_body (epilog : epred) : mpred :=
        (**
        The function consumes a step
        *)
        |>
        (* A [Defaulted] destructor has the empty body that clang gives
           implicit and defaulted destructors (see
           [Sema::DefineImplicitDestructor]); cpp2v prints those as
           [Defaulted]. Like [Sseq []] (see [wp_block]), it takes a step.
           Members and bases are destroyed below. *)
        let* :=
          match body with
          | Defaulted => fun k : Kpred => |={top}=>?upd |> |={top}=>?upd k Normal
          | CompilerProvided body
          | UserDefined body => wp tu (Remp (Some thisp) None Tvoid) body
          end%I
        in
        Kreturn_void epilog
      in
      match tu.(types) !! dtor.(d_class) with
      | Some (Gstruct s) =>
        letI* := wp_body in
        thisp |-> structR dtor.(d_class) 1$m **
        (**
        Destroy fields, object identity, and base classes (reverse
        order).

        TODO: This should probably be named.
        *)
        let* := wpd_members tu dtor.(d_class) thisp s.(s_fields) in
        let* := wp_revert_identity thisp tu dtor.(d_class) in
        let* := wpd_bases tu dtor.(d_class) thisp (List.map fst s.(s_bases)) in
        (**
        Return object's memory to the abstract machine.
        *)
        thisp |-> tblockR ty 1$m -*
        |={top}=>?upd |> Forall p : ptr, p |-> primR Tvoid 1$m Vvoid -*
        Q p
      | Some (Gunion u) =>
        (*
        The function epilog of a union destructor doesn't actually
        destroy anything because it isn't clear what to destroy (this
        is dictated by the C++ standard). Instead, the epilog provides
        a fancy update to destroy things (baked into [wp_body]).

        In practice, this means that programs can only destroy unions
        automatically where they can prove the active entry has a
        trivial destructor or is already destroyed.
        *)
        letI* := wp_body in
        thisp |-> tblockR ty 1$m **
        (
          thisp |-> tblockR ty 1$m -*
          |={top}=>?upd |> Forall p : ptr, p |-> primR Tvoid 1$m Vvoid -*
          Q p
        )
      | Some (Gvstruct vs) =>
        (*
        this is a structure with virtual bases.

        The destructor destroys the non-virtual part of the object
        only (fields, then non-virtual bases, in reverse order) and
        returns the memory of that part. The virtual bases are
        destroyed afterwards by whoever destroys the complete object
        (see [wp_destroy_vstruct]).

        As for constructors, object identities across virtual bases
        are not modeled yet, hence the [tu_no_vtables] side-condition.
        *)
        letI* := wp_body in
        [| tu_no_vtables tu dtor.(d_class) |] **
        let* := wpd_members tu dtor.(d_class) thisp vs.(vs_struct).(s_fields) in
        let* := wpd_nv_bases tu dtor.(d_class) thisp (rev (List.map fst vs.(vs_struct).(s_bases))) in
        thisp |-> nv_tblockR dtor.(d_class) 1$m -*
        |={top}=>?upd |> Forall p : ptr, p |-> primR Tvoid 1$m Vvoid -*
        Q p

      (* This includes [Gopaque]: a destructor destroys the members and
         bases, which an opaque record does not describe. Destructors of
         opaque records can be specified and called (see
         [wp_destroy_named]), but not verified. *)
      | _ => ERROR ("wp_dtor: not a structure or union")
      end%I
    | _ => ERROR "wp_dtor: expected one argument"
    end
  end.
mlock Definition wp_dtor `{Σ : cpp_logic, σ : genv} :=
  Cbn (Reduce (wp_dtor' true)).

Section wp_dtor.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (Q : ptr -> epred).

  Lemma wp_dtor_frame tu d args Q Q' :
    (**
    NOTE: We cannot presently weaken by [sub_module tu tu'] due to the
    embedded [wp_revert_identity].
    *)
    Forall p, Q p -* Q' p
    |-- wp_dtor tu d args Q -* wp_dtor tu d args Q'.
  Proof.
    iIntros "HQ". rewrite wp_dtor.unlock.
    repeat case_match; auto.
    all: iIntros "wp !>"; iRevert "wp".
    1,4,7: iIntros ">wp !> !>"; iMod "wp"; iModIntro; iRevert "wp".
    all: try (iApply wp_frame; [done|]; iIntros (?)).
    all: iApply Kreturn_void_frame.
    all: iIntros "($ & wp)"; iRevert "wp".
    all: try (iApply wpd_members_frame; [done|]).
    all: try (iApply wp_revert_identity_frame =>//).
    all: try (iApply wpd_bases_frame; [done|]).
    all: try iApply wpd_nv_bases_frame.
    all: iIntros "HR R"; iMod ("HR" with "R") as "HR"; iIntros "!> !> % R".
    all: iApply "HQ".
    all: iApply ("HR" with "R").
  Qed.

  (** Unsupported *)
  Lemma wp_dtor_shift tu d args Q :
    (|={top}=> wp_dtor tu d args (fun p => |={top}=> Q p))
    |-- wp_dtor tu d args Q.
  Abort.

  Lemma wp_dtor_intro tu d args Q :
    Cbn (Reduce (wp_dtor' false tu d args Q)) |-- wp_dtor tu d args Q.
  Proof.
    rewrite wp_dtor.unlock. repeat case_match; auto.
    all: iIntros "wp !>"; iRevert "wp".
    1,4,7: iIntros "wp !> !> !>"; iRevert "wp".
    all: try (iApply wp_frame; [done|]; iIntros (?)).
    all: iApply Kreturn_void_frame.
    all: iIntros "($ & wp)"; iRevert "wp".
    all: try (iApply wpd_members_frame; [done|]).
    all: try (iApply wp_revert_identity_frame =>//).
    all: try (iApply wpd_bases_frame; [done|]).
    all: try iApply wpd_nv_bases_frame.
    all: iIntros "HR R !>"; iSpecialize ("HR" with "R"); iIntros "!> % R".
    all: iApply ("HR" with "R").
  Qed.

  Lemma wp_dtor_elim tu d args Q :
    wp_dtor tu d args Q |-- Cbn (Reduce (wp_dtor' true tu d args Q)).
  Proof. by rewrite wp_dtor.unlock. Qed.
End wp_dtor.

(*
template<typename T>
struct optional {
  union U { T val; char nothing[sizeof(T)]; ~u() {} } u;
  bool has_value;
  ~optional() {
    if (has_value)
      val.~T();

  } // has_value.~bool(); u.~U();
}

p |-> classR .... -* |==> p |-> tblockR "class" 1

union { int x; short y; } u;
  // u |-> tblockR "U" 1
  // CREATE(0)
  u.x = 1;
  // DESTROY(0)
  // CREATE(1)
  u.y = 1;
  // DESTROY(1)
  // u |-> tblockR "U" 1

  // [CREATE(n)] implicit pick a union branch
  u |-> tblockR "U" 1 ==*
      u |-> (upaddingR "U" 1 ** ucaseR "U" 0 1 ** _field "x" |-> uninitR "U" 1)
  // [DESTROY(n)] implicit "destruction" of the union
  u |-> (upaddingR "U" 1 ** ucaseR "U" 0 1 ** _field "x" |-> uninitR "U" 1) ==*
      u |-> tblockR "U" 1
*)

Definition dtor_ok `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (dtor : Dtor) (spec : function_spec) : mpred :=
  [| type_of_spec spec = type_of_value (Odestructor dtor) |] **
  □ Forall (Q : ptr -> mpred) vals,
  spec.(fs_spec) vals Q -* wp_dtor tu dtor vals Q.
