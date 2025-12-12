(*
 * Copyright (c) 2020-2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import elpi.apps.locker.locker.
Require Import bluerock.iris.extra.proofmode.proofmode.	(** Early to get the right [ident] *)
Require Import bluerock.iris.extra.bi.ChargeCompat.
Require Import bluerock.iris.extra.bi.errors.
Require Import bluerock.lang.cpp.logic.entailsN.
Require Import bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.semantics.
Require Import bluerock.lang.cpp.logic.rep_proofmode.

Require Import bluerock.lang.cpp.logic.pred.
Require Import bluerock.lang.cpp.logic.path_pred.
Require Import bluerock.lang.cpp.logic.heap_pred.
Require Import bluerock.lang.cpp.logic.wp.
Require Import bluerock.lang.cpp.logic.builtins.
Require Import bluerock.lang.cpp.logic.cptr.
Require Import bluerock.lang.cpp.logic.const.
Require Import bluerock.lang.cpp.logic.initializers.
Require Import bluerock.lang.cpp.logic.translation_unit.
Require Import bluerock.lang.cpp.logic.destroy.

(* UPSTREAM. *)
Lemma wand_frame {PROP : bi} (R Q Q' : PROP) :
  Q -* Q' |--
  (R -* Q) -* (R -* Q').
Proof. iIntros "Q W R". iApply ("Q" with "(W R)"). Qed.

#[local] Set Printing Coercions.

#[local] Arguments ERROR {_ _} _%_bs.
#[local] Arguments UNSUPPORTED {_ _} _%_bs.
#[local] Arguments wpi : simpl never.

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
Part of [derivationsR path cls], but indexed by fuel [f].

TODO: Replace this with a version that is built by well-founded
recursion.
*)
#[local]
Definition derivationsR' `{Σ : cpp_logic, σ : genv} (tu : translation_unit) (q : cQp.t) :=
  fix derivationsR' (f : nat) (include_base : bool) (cls : globname) (path : list globname) : Rep :=
  match f with
  | 0 => ERROR "derivationsR: no fuel"
  | S f =>
    match tu.(types) !! cls with
    | Some (Gstruct st) =>
      (if include_base && has_vtable st then derivationR cls path q else emp) **
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
  derivationsR' tu q size include_base cls path.

Section derivationsR.
  Context `{Σ : cpp_logic, σ : genv}.

  Lemma derivationsR'_sub_module tu tu' q f include_base cls path :
    sub_module tu tu' ->
    derivationsR' tu q f include_base cls path
    |-- derivationsR' tu' q f include_base cls path.
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
    apply elem_of_list_In in H1.
    apply elem_of_list_lookup_1 in H1.
    destruct H1.
    eapply H0; eauto.
  Qed.

  Lemma derivationsR'_ok tu tu' (sub : sub_module tu tu') :
    forall f f' mdc (p : ptr) cls include_base q,
    f <= f' ->
        p |-> derivationsR' tu q f include_base cls mdc
    |-- p |-> derivationsR' tu' q f' include_base cls mdc ** [| supports_with_fuel tu cls f |].
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

  Lemma derivationsR'_ok_supports tu tu' (sub : sub_module tu tu') :
    forall cls f, supports_with_fuel tu cls f ->
             forall f' mdc (p : ptr) include_base q, f <= f' ->
        p |-> derivationsR' tu q f include_base cls mdc
    -|- p |-> derivationsR' tu' q f' include_base cls mdc.
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

End derivationsR.

(* conveniences for the common pattern *)
Notation init_derivationR cls path q :=
  (derivationR cls%_cpp_name (path%_cpp_name ++ [cls%_cpp_name]) q).

(**
[wp_init_identity this tu cls Q] updates the identities of [this] by
updating the [derivationR] of all base classes (transitively) and
producing the new identity for "this".
*)
Definition wp_init_identity `{Σ : cpp_logic, σ : genv} (p : ptr) (tu : translation_unit)
    (cls : globname) (Q : mpred) : mpred :=
  p |-> derivationsR tu false cls [] 1$m **
  (p |-> derivationsR tu true cls [cls] 1$m -* Q).

Section wp_init_identity.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (p : ptr) (Q : mpred).

  Lemma wp_init_identity_frame p tu tu' cls Q Q' :
    sub_module tu tu' ->
    Q' -* Q |-- wp_init_identity p tu cls Q' -* wp_init_identity p tu' cls Q.
  Proof.
    rewrite /wp_init_identity.
    iIntros (sub) "Q [X Y]".
    iDestruct (derivationsR_ok with "X") as "[X %]"; eauto.
    iFrame.
    iIntros "X". iApply "Q".
    iApply "Y".
    iApply derivationsR_ok_supports; eauto.
  Qed.
End wp_init_identity.

(**
[wp_revert_identity this tu cls Q] updates the identities of [this] by
taking the [identity] of this class and transitively updating the
[identity] of all base classes to remove [cls] as the most derived
class.
*)
Definition wp_revert_identity `{Σ : cpp_logic, σ : genv} (p : ptr) (tu : translation_unit)
    (cls : globname) (Q : mpred) : mpred :=
  p |-> derivationsR tu true cls [cls] 1$m **
  (p |-> derivationsR tu false cls [] 1$m -* Q).

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (p : ptr) (Q : mpred).

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
    iApply derivationsR_ok_supports; eauto.
  Qed.

  (** sanity chect that initialization and revert are inverses *)
  Lemma wp_init_revert p tu cls Q :
    let REQ := p |-> derivationsR tu false cls [] 1$m in
    REQ ** Q
    |-- wp_init_identity p tu cls (wp_revert_identity p tu cls (REQ ** Q)).
  Proof.
    rewrite /wp_revert_identity/wp_init_identity.
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
      |> wp tu ρ body (Kcleanup tu cleanup $ Kreturn $ fun x => |={top}=>?u |> Q x)
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
    iApply bind_vars_frame; [done|]. iIntros (??) "wp !>"; iRevert "wp".
    iApply wp_frame; [done|]. iIntros (?).
    iApply Kcleanup_frame; [done|].
    iApply Kreturn_frame. iIntros (?) "Q".
    iApply ("HQ" with "Q").
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
  | Some (UserDefined body) =>
    match args with
    | thisp :: rest_vals =>
      let ρ va := Remp (Some thisp) va m.(m_return) in
      letI* ρ, cleanup := bind_vars tu m.(m_arity) m.(m_params) rest_vals ρ in
      |> wp tu ρ body (Kcleanup tu cleanup $ Kreturn $ fun x => |={top}=>?u |> Q x)
    | _ => ERROR "wp_method: no arguments"
    end
  | Some _ => UNSUPPORTED "wp_method: defaulted methods"
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
    repeat case_match; auto.
    iApply bind_vars_frame; [done|]. iIntros (??) "wp !>"; iRevert "wp".
    iApply wp_frame; [done|]. iIntros (?).
    iApply Kcleanup_frame; [done|].
    iApply Kreturn_frame. iIntros (?) "Q".
    iApply ("HQ" with "Q").
  Qed.

  (** Unsupported *)
  Lemma wp_method_shift tu m args Q :
    (|={top}=> wp_method tu m args (fun p => |={top}=> Q p))
    |-- wp_method tu m args Q.
  Abort.

  Lemma wp_method_intro tu m args Q :
    Cbn (Reduce (wp_method' false tu m args Q)) |-- wp_method tu m args Q.
  Proof.
    rewrite wp_method.unlock. do 3!f_equiv.
    iApply bind_vars_frame; [done|]. iIntros (??) "wp !>"; iRevert "wp".
    iApply wp_frame; [done|]. iIntros (?).
    iApply Kcleanup_frame; [done|].
    iApply Kreturn_frame. auto.
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
      (* there is an initializer for this class *)
      wpi tu ρ cls this (Tnamed b) i (wpi_bases bases Q)
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
  | Break | Continue | ReturnVal _ => False
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
  | Some Defaulted => UNSUPPORTED "wp_ctor: defaulted constructors"
  | Some (UserDefined ib) =>
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
    iIntros "HQ". rewrite wp_ctor.unlock. repeat case_match; auto.
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
    rewrite wp_ctor.unlock. repeat case_match; auto.
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

Definition wpd_bases `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (cls : globname) (this : ptr) (bases : list globname) (Q : epred) : mpred :=
  let del_base base := FreeTemps.delete (Tnamed base) (this ,, _base cls base) in
  interp tu (FreeTemps.seqs_rev (List.map del_base bases)) Q.

Section with_cpp.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (Q : epred).

  Lemma wpd_bases_frame tu tu' cls this bases Q Q' :
    sub_module tu tu' ->
    Q -* Q' |-- wpd_bases tu cls this bases Q -* wpd_bases tu' cls this bases Q'.
  Proof. apply interp_frame_strong. Qed.
End with_cpp.

Definition wpd_members `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
    (cls : globname) (this : ptr) (members : list Member) (Q : epred) : mpred :=
  let del_member m := FreeTemps.delete m.(mem_type) (this ,, _field (Field cls m.(mem_name))) in
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
        let* :=
          match body with
          | Defaulted => fun k : Kpred => |={top}=>?upd k Normal
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
    1,3: iIntros ">wp !>"; iRevert "wp".
    3,4: iApply wp_frame; [done|]; iIntros (?).
    all: iApply Kreturn_void_frame.
    all: iIntros "($ & wp)"; iRevert "wp".
    2,4: iApply wpd_members_frame; [done|].
    2,3: iApply wp_revert_identity_frame =>//.
    2,3: iApply wpd_bases_frame; [done|].
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
    1,3: rewrite -fupd_intro.
    3,4: iApply wp_frame; [done|]; iIntros (?).
    all: iApply Kreturn_void_frame.
    all: iIntros "($ & wp)"; iRevert "wp".
    2,4: iApply wpd_members_frame; [done|].
    2,3: iApply wp_revert_identity_frame =>//.
    2,3: iApply wpd_bases_frame; [done|].
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
