(*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Stdlib.Lists.List.
Require Import bluerock.iris.extra.proofmode.proofmode.
Require Import bluerock.prelude.numbers.
Require Import bluerock.prelude.bool.
Require Import bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.semantics.
Require Import bluerock.iris.extra.bi.errors.
Require Import bluerock.lang.cpp.logic.pred.
Require Import bluerock.lang.cpp.logic.path_pred.
Require Import bluerock.lang.cpp.logic.heap_pred.
Require Import bluerock.lang.cpp.logic.wp.
Require Import bluerock.lang.cpp.logic.destroy.
Require Import bluerock.lang.cpp.logic.const.

#[local] Set Printing Coercions.

(**
The C++ language provides several types of initialization:
- default initialization <https://eel.is/c++draft/dcl.init#def:default-initialization>
- value initialization <https://eel.is/c++draft/dcl.init#def:value-initialization>
- zero initialization <https://eel.is/c++draft/dcl.init#def:zero-initialization>
- direct initialization <https://eel.is/c++draft/dcl.init#def:direct-initialization>

The BRiCk frontend resolves (via clang) the rules for which one of
these is used in each context. Therefore, in the semantics, we are
left with only two cases:

- default initialization (implemented by [default_initialize]), which
occurs when there is no expression used to initialize the value

- expression initialization (implemented by [wp_initialize]), which
occurs when there is an expression used to initialize the value.

Note that the frontend inserts constructor calls to default initialize
objects, so [Tnamed] types can *not* be default initialized.
*)

(** ** Default initilalization *)
(**
[default_initialize_array (default_initialize tu ty) tu ty len p Q]
initializes an array of type [ty[len]] at pointer [p] using
[default_initialize] (from right to left).

NOTE that default initialization of an array of constants is a
compile-time error, so we don't need to worry about that case.
Also, note that arrays of length 0 are not legal so we are
guaranteed to have to initialize a value which will result in an
[ERROR].
*)

#[local] Definition default_initialize_array_body `{Σ : cpp_logic, σ : genv}
    (u : bool) (default_initialize : ptr -> (FreeTemps -> epred) -> mpred)
    (tu : translation_unit) (ty : exprtype) (len : N) (p : ptr) (Q : FreeTemps -> epred) : mpred :=
  let folder i PP :=
    default_initialize (p ,, o_sub _ ty (Z.of_N i)) (fun free' => interp tu free' PP)
  in
  foldr folder (p |-> type_ptrR (Tarray ty len) -* |={top}=>?u Q FreeTemps.id) (seqN 0 len).

mlock
Definition default_initialize_array `{Σ : cpp_logic, σ : genv} :
  ∀ (default_initialize : ptr -> (FreeTemps -> epred) -> mpred)
    (tu : translation_unit) (ty : exprtype) (len : N) (p : ptr)
    (Q : FreeTemps -> epred), mpred :=
  Cbn (Reduce (default_initialize_array_body true)).

(**
[default_initialize tu ty p Q] default initializes the memory at [p]
according to the type [ty].

NOTE this assumes that the underlying memory has already been given to
the C++ abstract machine.

NOTE: <https://eel.is/c++draft/dcl.init#general-7>:
| (7) To default-initialize an object of type T means:
| (7.1) If T is a (possibly cv-qualified) class type ([class]), constructors are considered.
|       The applicable constructors are enumerated ([over.match.ctor]), and the best one for
|       the initializer () is chosen through overload resolution ([over.match]).
|       The constructor thus selected is called, with an empty argument list, to initialize
|       the object.
| (7.2) If T is an array type, each element is default-initialized.
| (7.3) Otherwise, no initialization is performed.

and [default_initialize] corresponds to [default-initialization] as
described above.
*)

#[local]
Definition default_initialize_body `{Σ : cpp_logic, σ : genv}
    (u : bool) (default_initialize : exprtype -> ptr -> (FreeTemps -> epred) -> mpred)
    (tu : translation_unit)
    (ty : exprtype) (p : ptr) (Q : FreeTemps -> epred) : mpred :=
  let ERROR := funI m => |={top}=>?u ERROR m in
  let UNSUPPORTED := funI m => |={top}=>?u UNSUPPORTED m in
  match ty with
  | Tnum _ _
  | Tchar_ _
  | Tptr _
  | Tbool
  | Tfloat_ _
  | Tnullptr
  | Tenum _ =>
    let rty := erase_qualifiers ty in
    p |-> uninitR rty 1$m -* |={top}=>?u Q FreeTemps.id

  | Tarray ety sz =>
    if bool_decide (0 < sz)%N then
      default_initialize_array (default_initialize ety) tu ety sz p (fun _ => Q FreeTemps.id)
    else
      ERROR "initializing an empty array"
  | Tincomplete_array _ => ERROR "default initialize incomplete array"
  | Tvariable_array _ _ => ERROR "default initialize variable array"

  | Tref _
  | Trv_ref _ => ERROR "default initialization of reference"
  | Tvoid => ERROR "default initialization of void"
  | Tfunction _ => ERROR "default initialization of functions"
  | Tmember_pointer _ _ => ERROR "default initialization of member pointers"
  | Tnamed _ => |={top}=>?u False (* default initialization of aggregates is done at elaboration time. *)

  | Tarch _ _ => UNSUPPORTED "default initialization of architecture type"
  | Tqualified q ty =>
    if q_volatile q then UNSUPPORTED "default initialize volatile"
    else if q_const q then ERROR "default initialize const"
    else default_initialize ty p Q
  | Tunsupported msg => UNSUPPORTED msg
  | Tdecltype _ => ERROR "default initialization requires a runtime type, got 'decltype(())'"
  | Texprtype _ => ERROR "default initialization requires a runtime type, got 'decltype()'"
  | Tauto => ERROR "default initialization requires a runtime type, got 'auto'"
  | Tparam _ | Tresult_param _ | Tresult_global _
  | Tresult_unop _ _ | Tresult_binop _ _ _
  | Tresult_call _ _ | Tresult_member_call _ _ _
  | Tresult_member _ _ | Tresult_parenlist _ _ => ERROR "default initialization requires a runtime type, got unresolved type"
  end%pstring%I.

mlock
Definition default_initialize `{Σ : cpp_logic, σ : genv} (tu : translation_unit)
  : ∀ (ty : exprtype) (p : ptr) (Q : FreeTemps -> epred), mpred :=
  fix default_initialize ty p Q {struct ty} :=
    Cbn (Reduce (default_initialize_body true) default_initialize tu ty p Q).

Section unfold.
  Context `{Σ : cpp_logic, σ : genv}.

  Lemma default_initialize_unfold ty tu :
    default_initialize tu ty =
    fun p Q => Cbn (Reduce (default_initialize_body true) (default_initialize tu) tu ty p Q).
  Proof. rewrite unlock. by destruct ty. Qed.
End unfold.

(**
Unfold for one type, failing if there's nothing to do.
*)
Ltac default_initialize_unfold :=
  lazymatch goal with
  | |- context [default_initialize _ ?ty] => rewrite !(default_initialize_unfold ty)
  | _ => fail "[default_initialize] not found"
  end.

Section default_initialize.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (Q : FreeTemps -> epred).
  Implicit Types (di : ptr -> (FreeTemps -> epred) -> mpred).

  #[local] Notation FRAME di di' :=
    (∀ p Q Q', (Forall f, Q f -* Q' f) |-- di p Q -* di' p Q')
    (only parsing).

  #[clearbody]
  Let default_initialize_array_frame' di di' tu tu' ty sz Q Q' (p : ptr) :
    FRAME di di' ->
    sub_module tu tu' ->
    (Forall f, Q f -* Q' f)
    |-- default_initialize_array di tu ty sz p Q -* default_initialize_array di' tu' ty sz p Q'.
  Proof.
    intros IHty Hsub. rewrite unlock.
    generalize dependent (p |-> type_ptrR (Tarray ty sz)).
    induction (seqN 0 sz) =>/=; intros.
    - iIntros "X a b". iApply "X". by iApply "a".
    - iIntros "F". iApply IHty.
      iIntros (?). iApply interp_frame_strong; [done|]. iApply (IHl with "F").
  Defined.

  #[clearbody]
  Let default_initialize_array_shift' di tu ty sz p Q :
    FRAME di di ->
    (∀ p Q, (|={top}=> di p (fun f => |={top}=> Q f)) |-- di p Q) ->
    (|={top}=> default_initialize_array di tu ty sz p (fun f => |={top}=> Q f))
    |-- default_initialize_array di tu ty sz p Q.
  Proof.
    intros Hframe Hshift. rewrite unlock.
    induction (seqN 0 sz); cbn.
    { iIntros ">HQ V". by iMod ("HQ" with "V"). }
    { iIntros "wp". iApply Hshift. iApply (Hframe with "[] wp"). iIntros (f) "wp !>".
      iApply (interp_frame with "[] wp"). rewrite -IHl. by iIntros "? !>". }
  Defined.

  (**
  TODO this should be generalized to different [σ] but, in that case
  it relies on the fact that [ty] is defined in both environments.
  *)
  Lemma default_initialize_frame tu tu' ty this Q Q' :
    sub_module tu tu' ->
    (Forall f, Q f -* Q' f)
    |-- default_initialize tu ty this Q -* default_initialize tu' ty this Q'.
  Proof.
    intros.
    move: this Q Q'. induction ty=>this Q Q'; default_initialize_unfold; try iIntros "? []".
    all: iIntros "HQ wp"; first
      [ by iIntros "R"; iMod ("wp" with "R") as "Q"; iApply ("HQ" with "Q")
      | by iMod "wp"; iExFalso; rewrite ?ERROR_elim ?UNSUPPORTED_elim
      | idtac ].
    { (* arrays *)
      case_match; eauto.
      iApply (default_initialize_array_frame' with "[HQ] wp"); [done..|].
      iIntros (?) "Q". iApply ("HQ" with "Q"). }
    { (* qualifiers *)
      case_match; eauto.
      case_match; first by iMod "wp"; iExFalso; rewrite ERROR_elim.
      iApply (IHty with "HQ wp"). }
  Qed.

  Lemma default_initialize_array_frame tu tu' ty sz Q Q' (p : ptr) :
    sub_module tu tu' ->
    (Forall f, Q f -* Q' f)
    |-- default_initialize_array (default_initialize tu ty) tu ty sz p Q
    -* default_initialize_array (default_initialize tu' ty) tu' ty sz p Q'.
  Proof. auto using default_initialize_frame. Qed.

  Lemma default_initialize_shift tu ty this Q :
    (|={top}=> default_initialize tu ty this (fun f => |={top}=> Q f))
    |-- default_initialize tu ty this Q.
  Proof.
    move: this Q. induction ty=>this Q; default_initialize_unfold;
      auto using fupd_elim, fupd_intro.
    all: try by iIntros ">HQ R"; iMod ("HQ" with "R").
    { (* arrays *)
      case_match.
      apply default_initialize_array_shift'; auto.
      intros. exact: default_initialize_frame.
      iIntros ">$". }
    { (* qualifiers *)
      do 2 (case_match; auto using fupd_elim, fupd_intro). }
  Qed.

  Lemma default_initialize_array_shift tu ty sz p Q :
    (|={top}=> default_initialize_array (default_initialize tu ty) tu ty sz p (fun f => |={top}=> Q f))
    |-- default_initialize_array (default_initialize tu ty) tu ty sz p Q.
  Proof.
    apply default_initialize_array_shift'.
    - intros. exact: default_initialize_frame.
    - apply default_initialize_shift.
  Qed.

  #[global] Instance: Params (@default_initialize) 7 := {}.
  #[local] Notation INIT R := (
    ∀ tu ty this,
    Proper (pointwise_relation _ R ==> R) (default_initialize tu ty this)
  ) (only parsing).
  #[global] Instance default_initialize_mono : INIT bi_entails.
  Proof.
    intros * Q1 Q2 HQ. iIntros "wp".
    iApply (default_initialize_frame with "[] wp"); [done|]. iIntros (free) "Q".
    by iApply HQ.
  Qed.
  #[global] Instance default_initialize_flip_mono : INIT (flip bi_entails).
  Proof. repeat intro. by apply default_initialize_mono. Qed.
  #[global] Instance default_initialize_proper : INIT equiv.
  Proof. intros * Q1 Q2 HQ. by split'; apply default_initialize_mono=>free; rewrite HQ. Qed.

  #[global] Instance: Params (@default_initialize_array) 9 := {}.
  #[local] Notation ARRAY R := (
    ∀ tu ty sz p,
    Proper (pointwise_relation _ R ==> R)
      (default_initialize_array (default_initialize tu ty) tu ty sz p)
  ) (only parsing).
  #[global] Instance default_initialize_array_mono : ARRAY bi_entails.
  Proof.
    intros * Q1 Q2 HQ. iIntros "wp".
    iApply (default_initialize_array_frame with "[] wp"); [done|].
    iIntros (free) "Q". by iApply HQ.
  Qed.
  #[global] Instance default_initialize_array_flip_mono : ARRAY (flip bi_entails).
  Proof. repeat intro. by apply default_initialize_array_mono. Qed.
  #[global] Instance default_initialize_array_proper : ARRAY equiv.
  Proof. intros * Q1 Q2 HQ. by split'; apply default_initialize_array_mono=>free; rewrite HQ. Qed.

  Lemma default_initialize_array_intro tu ty sz (p : ptr) Q :
    Cbn (Reduce (default_initialize_array_body false) (default_initialize tu ty) tu ty sz p Q)
    |-- default_initialize_array (default_initialize tu ty) tu ty sz p Q.
  Proof.
    rewrite default_initialize_array.unlock.
    induction (seqN 0 sz) as [|???IH]; cbn.
    { by rewrite -fupd_intro. }
    iIntros "wp". iApply (default_initialize_frame with "[] wp"); [done|].
    iIntros (?) "wp". iApply (interp_frame with "[] wp").
    iIntros "wp". iApply (IH with "wp").
  Qed.
  Lemma default_initialize_array_elim tu ty sz (p : ptr) Q :
    default_initialize_array (default_initialize tu ty) tu ty sz p Q
    |-- Cbn (Reduce (default_initialize_array_body true) (default_initialize tu ty) tu ty sz p Q).
  Proof. by rewrite default_initialize_array.unlock. Qed.

  Lemma default_initialize_intro tu ty (p : ptr) Q :
    Cbn (Reduce (default_initialize_body false) (default_initialize tu) tu ty p Q)
    |-- default_initialize tu ty p Q.
  Proof.
    rewrite (default_initialize_unfold ty). induction ty; first
      [ by auto using fupd_intro
      | by iIntros "HQ R"; iApply ("HQ" with "R")
      | idtac ].
    { (* arrays *)
      case_bool_decide; eauto. }
    { (* qualifiers *)
      destruct (q_volatile q); auto using fupd_intro.
      destruct (q_const q); auto using fupd_intro. }
  Qed.
  Lemma default_initialize_elim tu ty (p : ptr) Q :
    default_initialize tu ty p Q
    |-- Cbn (Reduce (default_initialize_body true) (default_initialize tu) tu ty p Q).
  Proof. rewrite default_initialize.unlock. by destruct ty. Qed.
End default_initialize.

(** ** Expression initialization *)

(* error used when using [e] to initialize a value of type [ty]. *)
Variant initializing_type (ty : type) (e : Expr) : Prop := ANY.

(**
[wp_initialize] provides "constructor" semantics for types. For
aggregates, simply delegates to [wp_init], but for primitives, the
semantics is to evaluate the primitive and initialize the location
with the value.

NOTE this assumes that the memory is coming from the C++ abstract
machine.

NOTE [wp_initialize] is very similar to [wp_init] except that
[wp_initialize] can be used to initialize all values (including
references) whereas [wp_init] is only safe to initialize
non-primitives (arrays and aggregates).
*)

(**
TODO (FM-3939): We disable compatibility with fancy updates for
[wp_initialize]. The presense of such updates interferes with
"learning" after [wp_initialize]; for example, we can learn equality
under a wand and an existential quantifier:
<<
∀ {A} (Vinj : A -> val) `{!Inj (=) (=) Vinj} (p : ptr) ty q (x1 : A) (Q : A -> mpred),
  p |-> tptstoR ty q (Vinj x1) -* (Exists x2, p |-> tptstoR ty q (Vinj x2) ** Q x2) |--
  p |-> tptstoR ty q (Vinj x1) -* p |-> tptstoR ty q (Vinj x1) ** Q x1.
>>
but such a rule would fail with [.. -* |={top}=> ..] in place of the
magic wands.
*)
#[local] Notation fupd_compatible := false (only parsing).

(* BEGIN wp_initialize *)
#[local]
Definition wp_initialize_unqualified_body `{Σ : cpp_logic, σ : genv}
    (u : bool) (tu : translation_unit) (ρ : region)
    (cv : type_qualifiers) (ty : decltype)
    (addr : ptr) (init : Expr) (Q : FreeTemps -> epred) : mpred :=
  let UNSUPPORTED := funI m => |={top}=>?u UNSUPPORTED m in
  if q_volatile cv then False%I
  else
    match ty with
    | Tvoid =>
      (*
      [wp_initialize] is used to `return` from a function. The following
      is legal in C++:
      <<
        void f();
        void g() { return f(); }
      >>
      *)
      letI* v, frees := wp_operand tu ρ init in
      let qf := cQp.mk (q_const cv) 1 in
      [| v = Vvoid |] **

      (**
      [primR] is enough because C++ code never uses the raw bytes
      underlying an inhabitant of type void.
      *)
      (addr |-> primR Tvoid qf Vvoid -* |={top}=>?u Q frees)

    | Tptr _
    | Tmember_pointer _ _
    | Tbool
    | Tnum _ _
    | Tchar_ _
    | Tenum _
    | Tfloat_ _
    | Tnullptr =>
      letI* v, free := wp_operand tu ρ init in
      let qf := cQp.mk (q_const cv) 1 in
      addr |-> tptsto_fuzzyR (erase_qualifiers ty) qf v -* |={top}=>?u Q free

      (* non-primitives are handled via prvalue-initialization semantics *)
    | Tarray _ len =>
        if bool_decide (0 < len)%N then
          wp_init tu ρ (tqualified cv ty) addr init Q
        else
          UNSUPPORTED (initializing_type ty init)
    | Tnamed _ => wp_init tu ρ (tqualified cv ty) addr init Q
    | Tincomplete_array _ => UNSUPPORTED (initializing_type ty init)
    | Tvariable_array _ _ => UNSUPPORTED (initializing_type ty init)

    | Tref ty =>
      let rty := Tref $ erase_qualifiers ty in
      letI* p, free := wp_glval tu ρ init in (* TODO this needs to permit initialization from xval if [ty] is <<const>> *)
      let qf := cQp.mk (q_const cv) 1 in
      (*
      [primR] is enough because C++ code never uses the raw bytes
      underlying an inhabitant of a reference type.

      TODO: [ref]s are never mutable, but we use [qf] here for
      compatibility with [implicit_destruct_struct]
      *)
      addr |-> primR rty qf (Vref p) -* |={top}=>?u Q free

    | Trv_ref ty =>
      let rty := Tref $ erase_qualifiers ty in
      letI* p, free := wp_xval tu ρ init in
      let qf := cQp.mk (q_const cv) 1 in
      (*
      [primR] is enough because C++ code never uses the raw bytes
      underlying an inhabitant of a reference type.

      TODO: [ref]s are never mutable, but we use [qf] here for
      compatibility with [implicit_destruct_struct]
      *)
      addr |-> primR rty qf (Vref p) -* |={top}=>?u Q free

    | Tfunction _ => UNSUPPORTED (initializing_type ty init)

    | Tqualified _ ty => |={top}=>?u False (* unreachable *)
    | Tarch _ _ => UNSUPPORTED (initializing_type ty init)
    | Tunsupported _ => UNSUPPORTED (initializing_type ty init)
    | Tdecltype _ =>  UNSUPPORTED (initializing_type ty init)
    | Texprtype _ =>  UNSUPPORTED (initializing_type ty init)
    | Tparam _ | Tresult_param _ | Tresult_global _
    | Tresult_unop _ _ | Tresult_binop _ _ _
    | Tresult_call _ _ | Tresult_member_call _ _ _
    | Tresult_member _ _ | Tresult_parenlist _ _
    | Tauto => UNSUPPORTED (initializing_type ty init)
    end%I.

mlock
Definition wp_initialize_unqualified `{Σ : cpp_logic, σ : genv} :
  ∀ (tu : translation_unit) (ρ : region)
    (cv : type_qualifiers) (ty : decltype)
    (addr : ptr) (init : Expr) (Q : FreeTemps -> epred), mpred :=
  Cbn (Reduce (wp_initialize_unqualified_body fupd_compatible)).

Definition wp_initialize `{Σ : cpp_logic, σ : genv} (tu : translation_unit) (ρ : region)
    (qty : decltype) (addr : ptr) (init : Expr) (Q : FreeTemps -> epred) : mpred :=
  qual_norm (wp_initialize_unqualified tu ρ) qty addr init Q.
#[global] Hint Opaque wp_initialize : typeclass_instances.
#[global] Arguments wp_initialize {_ _ _ _} _ _ !_ _ _ _ / : assert.
(* END wp_initialize *)

Definition heap_type_of (t : type) : type :=
  match erase_qualifiers t with
  | Trv_ref ty => Tref ty
  | t => t
  end.

Lemma wp_initialize_unqualified_well_typed `{Σ : cpp_logic, σ : genv}
  tu ρ cv ty addr init (Q : FreeTemps.t -> epred) :
      wp_initialize_unqualified tu ρ cv ty addr init (fun free => reference_to (heap_type_of ty) addr -* Q free)
  |-- wp_initialize_unqualified tu ρ cv ty addr init Q.
Proof.
  rewrite wp_initialize_unqualified.unlock.
  case_match; eauto.
  case_match; subst; eauto.
  all: try (iApply wp_operand_frame; [ done | ];
    iIntros (??) "X Y";
    iDestruct (observe (reference_to _ _) with "Y") as "#?";
    iApply ("X" with "Y");
    rewrite -reference_to_erase; done).
  - iApply wp_glval_frame; [ done | ];
      iIntros (??) "X Y";
      iDestruct (observe (reference_to _ _) with "Y") as "#?".
      iApply ("X" with "Y"). rewrite /heap_type_of/=. done.
  - iApply wp_xval_frame; [ done | ];
      iIntros (??) "X Y";
      iDestruct (observe (reference_to _ _) with "Y") as "#?";
      iApply ("X" with "Y").
    rewrite /heap_type_of/=. done.
  - iApply wp_operand_frame; [ done | ].
    iIntros (??) "[$ X] Y".
    iDestruct (observe (reference_to _ _) with "Y") as "#?";
    iApply ("X" with "Y"); eauto.
  - (* arrays *)
    case_bool_decide; eauto.
    etransitivity; [ | apply wp_init_well_typed ].
    iApply wp_init_frame; [ done | ].
    iIntros (?) "X Y". iApply "X".
    rewrite /heap_type_of/=.
    rewrite reference_to_erase/=/tqualified'.
    destruct cv; simpl; eauto.
  - etransitivity; [ | apply wp_init_well_typed ].
    iApply wp_init_frame; [ done | ].
    iIntros (?) "X Y". iApply "X".
    rewrite (reference_to_erase (Tnamed gn)).
    rewrite reference_to_erase/=/tqualified'.
    destruct cv; simpl; eauto.
Qed.

(**
[wpi cls this init Q] evaluates the initializer [init] from the object
[thisp] (of type [Tnamed cls]) and then proceeds as [Q].

NOTE that temporaries introduced by the evaluation of [init] are
cleaned up before [Q] is run ([Q] does not have a [FreeTemps]
argument). This is because initialization is considered a full
expression.

See [https://eel.is/c++draft/class.init#class.base.init-note-2].
*)
Definition wpi `{Σ : cpp_logic, σ : genv} (tu : translation_unit) (ρ : region)
    (cls : globname) (thisp : ptr) (ty : type) (init : Initializer) (Q : epred) : mpred :=
  let p' := thisp ,, offset_for cls init.(init_path) in
  letI* free := wp_initialize tu ρ ty p' init.(init_init) in
  letI* := interp tu free in
  Q.
#[global] Hint Opaque wpi : typeclass_instances.
#[global] Arguments wpi {_ _ _ _} _ _ _ _ _ _ _ / : assert.

(*
All framing lemmas *should* work with [genv] weakening, but that
requires some additional side-conditions on paths that we can't prove
right now. So, for the time being, we prove [_frame] lemmas without
[genv] weakening.
*)

Section wp_initialize.
  Context `{Σ : cpp_logic, σ : genv}.
  Implicit Types (Q : FreeTemps -> epred).

  (** [wp_initialize_unqualified] *)

  Lemma wp_initialize_unqualified_intro tu ρ cv ty obj e Q :
    Cbn (Reduce wp_initialize_unqualified_body false) tu ρ cv ty obj e Q
    |-- wp_initialize_unqualified tu ρ cv ty obj e Q.
  Proof.
    rewrite wp_initialize_unqualified.unlock. destruct ty; auto.
    all:
      repeat case_match;
      lazymatch goal with
      | |- context [wp_operand] => iApply wp_operand_frame; [done|]
      | |- context [wp_lval] => iApply wp_lval_frame; [done|]
      | |- context [wp_xval] => iApply wp_xval_frame; [done|]
      | |- context [wp_init] => iApply wp_init_frame; [done|]
      | _ => idtac
      end.
  (* Relevant to [fupd_compatible = true]
    all: first
      [ iIntros (??) "HQ R"; iApply ("HQ" with "R")
      | iIntros (??) "[$ HQ] R"; iApply ("HQ" with "R")
      | idtac ].
  *)
  Qed.

  Lemma wp_initialize_unqualified_elim tu ρ cv ty obj e Q :
    wp_initialize_unqualified tu ρ cv ty obj e Q
    |-- Cbn (Reduce wp_initialize_unqualified_body fupd_compatible) tu ρ cv ty obj e Q.
  Proof. by rewrite wp_initialize_unqualified.unlock. Qed.

  (**
  For value types, [wp_initialize -|- wp_operand].

  Compared to unfolding, these [_val] lemmas treat value types
  uniformly.
  *)

  (**
  [can_init ty e] is a side-condition for introducing [wp_initialize]
  with value type [ty] and expression [e], serving the conjunct [v =
  Vvoid] in [wp_initialize_unqualified]'s [Tvoid] case.
  *)
  Definition can_init (ty : type) (e : Expr) : bool :=
    bool_decide (ty = Tvoid) ==>
    bool_decide (type_of e = Tvoid).

  Lemma can_init_void e : can_init Tvoid e -> type_of e = Tvoid.
  Proof.
    move/implyP. rewrite bool_decide_true//.
    by move/(_ I)/bool_decide_unpack.
  Qed.

  #[local] Notation VAL_INIT u tu ρ cv ty addr init Q := (Cbn (
    let cv' := cv in (* to establish scopes *)
    if q_volatile cv' then False
    else
      letI* v, free := wp_operand tu ρ init in
      let qf := cQp.mk (q_const cv') 1 in
      addr |-> tptsto_fuzzyR (erase_qualifiers ty) qf v -* |={top}=>?u Q free
  )%I) (only parsing).

  Lemma wp_initialize_unqualified_intro_val tu ρ cv ty (addr : ptr) init Q :
    can_init ty init ->
    ~~ is_qualified ty -> is_value_type ty ->
    VAL_INIT false tu ρ cv ty addr init Q
    |-- wp_initialize_unqualified tu ρ cv ty addr init Q.
  Proof.
    intros Hty ??. rewrite -wp_initialize_unqualified_intro.
    case_match; eauto.
    destruct ty; try solve [ inversion H0 | eauto ].
    (* void *)
    iIntros "wp /=".
    iApply wp_operand_well_typed.
    iApply (wp_operand_wand with "wp"). iIntros (v f).
    rewrite can_init_void// has_type_void. iIntros "HQ ->".
    rewrite tptsto_fuzzyR_Vvoid_primR. by iFrame "HQ".
  Qed.

  Lemma wp_initialize_unqualified_elim_val tu ρ cv ty addr init Q :
    ~~ is_qualified ty -> is_value_type ty ->
    wp_initialize_unqualified tu ρ cv ty addr init Q
    |-- VAL_INIT fupd_compatible tu ρ cv ty addr init Q.
  Proof.
    intros. rewrite wp_initialize_unqualified_elim.
    case_match; eauto. destruct ty; try done.
    (* void *)
    iIntros "wp".
    iApply (wp_operand_wand with "wp"). iIntros (v f) "(-> & HQ) R".
    iApply ("HQ" with "[R]"). cbn. by rewrite tptsto_fuzzyR_Vvoid_primR.
  Qed.

  (**
  For aggregate types, [wp_initialize -|- wp_init].
  *)

  Lemma wp_initialize_unqualified_elim_aggregate tu ρ cv ty qty addr init Q :
    qty ≡ Tqualified cv ty -> is_aggregate_type ty ->
    wp_initialize_unqualified tu ρ cv ty addr init Q |-- wp_init tu ρ qty addr init Q.
  Proof.
    intros Heq ?. rewrite wp_initialize_unqualified_elim.
    case_match; [ iIntros "[]" | ]; destruct ty; first
      [ by rewrite ?(UNSUPPORTED_elim, bi.False_elim)
      | idtac ].
    all: try by rewrite tqualified_equiv Heq.
  (* Relevant to [fupd_compatible = true] in [wp_initialize]
    (** Absurd cases *)
    all: rewrite -fupd_wp_init; iMod 1; iExFalso; by rewrite ?UNSUPPORTED_elim.
  *)
  Qed.
  Lemma wp_initialize_unqualified_intro_aggregate tu ρ cv ty qty addr init Q :
    qty ≡ Tqualified cv ty -> ~~ is_qualified ty -> is_aggregate_type ty ->
        (if q_volatile cv then False else wp_init tu ρ qty addr init Q)
    |-- wp_initialize_unqualified tu ρ cv ty addr init Q.
  Proof.
    intros Heq ??. rewrite -wp_initialize_unqualified_intro.
    case_match; [ iIntros "[]" | ].
    destruct ty; try done.
    all: by rewrite tqualified_equiv Heq.
  Qed.

  (** Properties *)

  Lemma wp_initialize_unqualified_frame tu tu' ρ obj cv ty e Q Q' :
    sub_module tu tu' ->
    (Forall free, Q free -* Q' free)
    |-- wp_initialize_unqualified tu ρ cv ty obj e Q -* wp_initialize_unqualified tu' ρ cv ty obj e Q'.
  Proof.
    intros. iIntros "HQ'". destruct ty; rewrite unlock; auto.
    all: case_match; eauto.
    all:
      repeat case_match;
      lazymatch goal with
      | |- context [wp_operand] => iApply wp_operand_frame; [done|]
      | |- context [wp_lval] => iApply wp_lval_frame; [done|]
      | |- context [wp_glval] => iApply wp_glval_frame; [done|]
      | |- context [wp_xval] => iApply wp_xval_frame; [done|]
      | |- context [wp_init] => iApply wp_init_frame; [done|]
      | _ => idtac
      end;
      first
        [ by iIntros (??) "HQ ?"; iApply "HQ'"; iApply "HQ"
        | by iIntros (?) "?"; iApply "HQ'"
        | eauto ].
    (* void *)
    iIntros (??) "($ & HQ) ?". iApply "HQ'". by iApply "HQ".
  Qed.

  Lemma wp_initialize_unqualified_shift tu ρ cv ty obj e Q :
    Cbn (|={top}=>?fupd_compatible wp_initialize_unqualified tu ρ cv ty obj e (fun free => |={top}=>?fupd_compatible Q free))
    |-- wp_initialize_unqualified tu ρ cv ty obj e Q.
  Proof.
    destruct ty; rewrite unlock; auto using fupd_elim, fupd_intro.
  (* Relevant to [fupd_compatible = true]
    all: iIntros "wp".
    all: lazymatch goal with
    | |- context [wp_operand] => iApply wp_operand_shift; iApply (wp_operand_frame with "[] wp"); [done|]
    | |- context [wp_lval] => iApply wp_lval_shift; iApply (wp_lval_frame with "[] wp"); [done|]
    | |- context [wp_xval] => iApply wp_xval_shift; iApply (wp_xval_frame with "[] wp"); [done|]
    | |- context [wp_init] => iApply wp_init_shift; iMod "wp"; by iModIntro
    | _ => idtac
    end.
    all: try by iIntros (??) "HQ !> R"; iMod ("HQ" with "R").
    (* void *)
    iIntros (??) "($ & HQ) !> R". by iMod ("HQ" with "R").
  *)
  Qed.

  #[global] Instance: Params (@wp_initialize_unqualified) 10 := {}.
  #[local] Notation BODY R := (
    ∀ tu ρ cv ty obj init,
    Proper (pointwise_relation _ R ==> R) (wp_initialize_unqualified tu ρ cv ty obj init)
  ) (only parsing).
  #[global] Instance wp_initialize_unqualified_mono : BODY bi_entails.
  Proof.
    intros * Q1 Q2 HQ. iIntros "wp".
    iApply (wp_initialize_unqualified_frame with "[] wp"); [done|]. iIntros (free) "Q".
    by iApply HQ.
  Qed.
  #[global] Instance wp_initialize_unqualified_flip_mono : BODY (flip bi_entails).
  Proof. repeat intro. by apply wp_initialize_unqualified_mono. Qed.
  #[global] Instance wp_initialize_unqualified_proper : BODY equiv.
  Proof. intros * Q1 Q2 HQ. by split'; apply wp_initialize_unqualified_mono=>free; rewrite HQ. Qed.

  (** [wp_initialize] *)

  Lemma wp_initialize_ok tu ρ qty :
    qual_norm_spec (wp_initialize_unqualified tu ρ) QM qty (wp_initialize tu ρ qty).
  Proof. apply qual_norm_ok. Qed.

  Lemma wp_initialize_qual_norm tu ρ qty :
    wp_initialize tu ρ qty = qual_norm (wp_initialize_unqualified tu ρ) qty.
  Proof. done. Qed.

  Lemma wp_initialize_decompose_type tu ρ qty :
    wp_initialize tu ρ qty =
      let p := decompose_type qty in
      wp_initialize_unqualified tu ρ p.1 p.2.
  Proof.
    by rewrite wp_initialize_qual_norm qual_norm_decompose_type.
  Qed.

  Lemma wp_initialize_intro tu ρ ty addr init Q :
    qual_norm (fun cv rty => Cbn (Reduce wp_initialize_unqualified_body false) tu ρ cv rty addr init Q) ty
    |-- wp_initialize tu ρ ty addr init Q.
  Proof.
    rewrite qual_norm_decompose_type wp_initialize_decompose_type.
    apply wp_initialize_unqualified_intro.
  Qed.

  Lemma wp_initialize_elim tu ρ ty addr init Q :
    wp_initialize tu ρ ty addr init Q
    |-- qual_norm (fun cv rty => Cbn (Reduce wp_initialize_unqualified_body fupd_compatible) tu ρ cv rty addr init Q) ty.
  Proof.
    rewrite wp_initialize_decompose_type qual_norm_decompose_type.
    apply wp_initialize_unqualified_elim.
  Qed.

  (**
  Compared to unfolding, these [_val] lemmas treat value types
  uniformly.
  *)
  Lemma wp_initialize_intro_val tu ρ ty (addr : ptr) init Q :
    can_init (drop_qualifiers ty) init -> is_value_type ty ->
    VAL_INIT false tu ρ (qual_norm (fun cv _ => cv) ty) ty addr init Q
    |-- wp_initialize tu ρ ty addr init Q.
  Proof.
    rewrite drop_qualifiers_decompose_type.
    rewrite is_value_type_decompose_type wp_initialize_decompose_type.
    rewrite qual_norm_decompose_type erase_qualifiers_decompose_type.
    have := is_qualified_decompose_type (type_of init). cbn. intros.
    by rewrite -wp_initialize_unqualified_intro_val.
  Qed.

  Lemma wp_initialize_elim_val tu ρ ty addr init Q :
    is_value_type ty ->
    wp_initialize tu ρ ty addr init Q
    |-- VAL_INIT fupd_compatible tu ρ (qual_norm (fun cv _ => cv) ty) ty addr init Q.
  Proof.
    rewrite is_value_type_decompose_type wp_initialize_decompose_type.
    rewrite qual_norm_decompose_type erase_qualifiers_decompose_type.
    have := is_qualified_decompose_type ty.
    apply wp_initialize_unqualified_elim_val.
  Qed.

  Lemma wp_initialize_elim_aggregate tu ρ ty addr init Q :
    is_aggregate_type ty ->
    wp_initialize tu ρ ty addr init Q |-- wp_init tu ρ ty addr init Q.
  Proof.
    rewrite is_aggregate_type_decompose_type wp_initialize_decompose_type.
    apply wp_initialize_unqualified_elim_aggregate.
    by rewrite decompose_type_equiv.
  Qed.

  Lemma wp_initialize_intro_aggregate tu ρ ty addr init Q :
    is_aggregate_type ty ->
    TCEq (is_volatile ty) false ->
    wp_init tu ρ ty addr init Q |-- wp_initialize tu ρ ty addr init Q.
  Proof.
    rewrite is_aggregate_type_decompose_type wp_initialize_decompose_type.
    rewrite /decompose_type. intros.
    rewrite -wp_initialize_unqualified_intro_aggregate; [| | eauto | eauto ].
    { have->: q_volatile (qual_norm (fun cv t => (cv,t)) ty).1 = false.
      { rewrite 2!qual_norm_map. simpl. inversion H0. done. }
      reflexivity. }
    by rewrite decompose_type_equiv.
  Qed.

  Lemma wp_initialize_frame tu tu' ρ obj ty e Q Q' :
    sub_module tu tu' ->
    (Forall free, Q free -* Q' free)
    |-- wp_initialize tu ρ ty obj e Q -* wp_initialize tu' ρ ty obj e Q'.
  Proof.
    intros. rewrite /wp_initialize/qual_norm.
    induction (wp_initialize_ok tu ρ ty); last done.
    rewrite !qual_norm'_unqual//. exact: wp_initialize_unqualified_frame.
  Qed.

  Lemma wp_initialize_shift tu ρ ty obj e Q :
    Cbn (|={top}=>?fupd_compatible wp_initialize tu ρ ty obj e (fun free => |={top}=>?fupd_compatible Q free))
    |-- wp_initialize tu ρ ty obj e Q.
  Proof.
    rewrite /wp_initialize/qual_norm.
    induction (wp_initialize_ok tu ρ ty); last done.
    rewrite !qual_norm'_unqual//.
  (* Relevant to [fupd_compatible = true]
    apply wp_initialize_unqualified_shift.
  *)
  Qed.

  #[global] Instance: Params (@wp_initialize) 9 := {}.
  #[local] Notation INIT R := (
    ∀ tu ρ ty obj init,
    Proper (pointwise_relation _ R ==> R) (wp_initialize tu ρ ty obj init)
  ) (only parsing).
  #[global] Instance wp_initialize_mono : INIT bi_entails.
  Proof.
    intros * Q1 Q2 HQ. iIntros "wp".
    iApply (wp_initialize_frame with "[] wp"); [done|]. iIntros (free) "Q".
    by iApply HQ.
  Qed.
  #[global] Instance wp_initialize_flip_mono : INIT (flip bi_entails).
  Proof. repeat intro. by apply wp_initialize_mono. Qed.
  #[global] Instance wp_initialize_proper : INIT equiv.
  Proof. intros * Q1 Q2 HQ. by split'; apply wp_initialize_mono=>free; rewrite HQ. Qed.

  Lemma wp_initialize_wand tu ρ obj ty e Q Q' :
    wp_initialize tu ρ ty obj e Q
    |-- (Forall free, Q free -* Q' free) -* wp_initialize tu ρ ty obj e Q'.
  Proof. by iIntros "H Y"; iRevert "H"; iApply wp_initialize_frame. Qed.

  Inductive wp_initialize_decomp_spec tu ρ ty (addr : ptr) init Q : mpred -> Prop :=
  | WpInitVolatile cv ty' : (cv, ty') = decompose_type ty ->
                            q_volatile cv ->
                          wp_initialize_decomp_spec tu ρ ty addr init Q False
  | WpInitScalar cv ty' : is_scalar_type ty' ->
                         (cv, ty') = decompose_type ty ->
                         ~~q_volatile cv ->
                         wp_initialize_decomp_spec tu ρ ty addr init Q (
                             letI* v, free := wp_operand tu ρ init in
                               let qf := cQp.mk (q_const cv) 1 in
                               addr |-> tptsto_fuzzyR (erase_qualifiers ty) qf v -* Q free
                           )
  | WpInitRef cv ty' : drop_qualifiers ty = Tref ty' ->
                      wp_initialize_decomp_spec tu ρ ty addr init Q (
                          let rty := Tref $ erase_qualifiers ty' in
                          letI* p, free := wp_lval tu ρ init in
                            let qf := cQp.mk (q_const cv) 1 in
                            addr |-> primR rty qf (Vref p) -* Q free
                        )
  | WpInitRvRef cv ty' : drop_qualifiers ty = Trv_ref ty' ->
                        wp_initialize_decomp_spec tu ρ ty addr init Q (
                            let rty := Tref $ erase_qualifiers ty' in
                            letI* p, free := wp_xval tu ρ init in
                              let qf := cQp.mk (q_const cv) 1 in
                              addr |-> primR rty qf (Vref p) -* Q free
                          )
  | WpInitVoid cv : decompose_type ty = (cv, Tvoid) ->
                    ~~q_volatile cv ->
                    wp_initialize_decomp_spec tu ρ ty addr init Q (
                        letI* v, frees := wp_operand tu ρ init in
                          let qf := cQp.mk (q_const cv) 1 in
                          [| v = Vvoid |] **
                            (addr |-> primR Tvoid qf Vvoid -* Q frees)
                      )
  | WpInitAggreg cv ty' : is_aggregate_type ty' ->
                         (cv, ty') = decompose_type ty ->
                         ~~q_volatile cv ->
                         wp_initialize_decomp_spec tu ρ ty addr init Q (
                             wp_init tu ρ (tqualified cv ty') addr init Q
                           )
  | WpInitArray cv ety len (ty' := Tarray ety len) :
    (cv, Tarray ety len) = decompose_type ty ->
    ~~q_volatile cv ->
    wp_initialize_decomp_spec tu ρ ty addr init Q (
        if bool_decide (0 < len)%N then
          wp_init tu ρ (tqualified cv ty') addr init Q
        else
          UNSUPPORTED (initializing_type ty' init)
      )
  | WpInitFuncArch cv ty' : match ty' with
                        | Tfunction _
                        | Tarch _ _
                        | Tincomplete_array _
                        | Tvariable_array _ _ => true
                        | _ => false
                        end ->
                         (cv, ty') = decompose_type ty ->
                         ~~q_volatile cv ->
                        wp_initialize_decomp_spec tu ρ ty addr init Q (
                            UNSUPPORTED (initializing_type ty' init)
                          )
  | WpInitUnsupported cv msg : decompose_type ty = (cv, Tunsupported msg) ->
                          wp_initialize_decomp_spec tu ρ ty addr init Q False
  .

  Lemma wp_initialize_decomp_ok tu ρ ty addr e Q :
    wp_initialize_decomp_spec tu ρ ty addr e Q (wp_initialize tu ρ ty addr e Q).
  Proof.
    rewrite wp_initialize_qual_norm wp_initialize_unqualified.unlock.
    case: qual_norm_decomp_ok=>q t.
    case Ht: t.
    all: case_match; try solve [ intros; econstructor; eauto ].
    all: try (rewrite [decompose_type _]surjective_pairing=>[][Hq Hty];
      rewrite Hty -erase_qualifiers_decompose_type;
      econstructor; [ | rewrite [decompose_type _]surjective_pairing -Hq -Hty // | rewrite H ]; eauto).


(*    all: try by rewrite [decompose_type _]surjective_pairing=>[][Hq Hty];
      rewrite Hty -erase_qualifiers_decompose_type;
      econstructor; last rewrite [decompose_type _]surjective_pairing -Hq -Hty //. *)
    all: try by rewrite [decompose_type _]surjective_pairing=>[][Hq Hty];
      econstructor;
      rewrite Hty; apply: drop_qualifiers_decompose_type.
    all: try by rewrite [decompose_type _]surjective_pairing=>[][Hq Hty]; econstructor;
      try solve [ done | rewrite //= [decompose_type _]surjective_pairing -Hq -Hty // | rewrite H // ].
    (*
    { (* Tqualified *)
      rewrite [decompose_type _]surjective_pairing;
        move: (is_qualified_decompose_type ty)=>/[swap][][] _ <-.
      by simpl. }
    { (* Tunsupported *)
      intros. rewrite UNSUPPORTED.unlock. exact: WpInitUnsupported. }
  Qed. *) Admitted. (* TODO: this would be improved by eliminating these cases using dependency *)

  (** [wpi] *)

  Lemma wpi_frame tu tu' ρ cls this ty e (Q Q' : epred) :
    sub_module tu tu' ->
    Q -* Q' |-- wpi tu ρ cls this ty e Q -* wpi tu' ρ cls this ty e Q'.
  Proof.
    intros. iIntros "HQ". rewrite /wpi.
    iApply wp_initialize_frame; [done|]. iIntros (free).
    by iApply interp_frame_strong.
  Qed.

  Lemma wpi_shift tu ρ cls this ty e (Q : epred) :
    Cbn (|={top}=>?fupd_compatible wpi tu ρ cls this ty e (|={top}=>?fupd_compatible Q))
    |-- wpi tu ρ cls this ty e Q.
  Proof.
    done.
  (* Relevant to [fupd_compatible = true]
    rewrite /wpi. iIntros "wp".
    iApply wp_initialize_shift. iMod "wp".
    iApply (wp_initialize_frame with "[] wp"); [done|]. iIntros (f) "wp !>".
    by iApply interp_fupd.
  *)
  Qed.

  #[global] Instance: Params (@wpi) 9 := {}.
  #[local] Notation WPI R := (
    ∀ tu ρ cls this ty e,
    Proper (R ==> R) (wpi tu ρ cls this ty e)
  ) (only parsing).
  #[global] Instance wpi_mono : WPI bi_entails.
  Proof.
    intros * Q1 Q2 HQ. iIntros "wp".
    iApply (wpi_frame with "[] wp"); [done|]. iIntros "Q".
    by iApply HQ.
  Qed.
  #[global] Instance wpi_flip_mono : WPI (flip bi_entails).
  Proof. repeat intro. by apply wpi_mono. Qed.
  #[global] Instance wpi_proper : WPI equiv.
  Proof. intros * Q1 Q2 HQ. by split'; apply wpi_mono; rewrite HQ. Qed.
End wp_initialize.
