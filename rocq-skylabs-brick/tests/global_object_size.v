(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.lang.cpp.logic.heap_pred.
Require Import skylabs.lang.cpp.logic.pred.
Require Import skylabs.lang.cpp.logic.path_pred.
Require Import skylabs.lang.cpp.logic.
Require Import skylabs.iris.extra.proofmode.proofmode.

Import ChargeNotation.
Set Default Proof Using "Type*".

(* The compiler extension in the original counterexample creates a zero-sized
   class. Checking only whether a global's type is a zero-length array misses it. *)
Definition zero_global_struct : Struct :=
  Build_Struct []
    [mkMember (Nid "bytes"%pstring) "unsigned char[0]"%cpp_type false None {| li_offset := 0 |}]
    [] [] "Empty::~Empty()"%cpp_name true None POD 0 1.

Definition global_size_env (ty : type) : genv :=
  {| genv_tu := makeTranslationUnit
       {[ "object"%cpp_name := Ovar ty global_init.NoInit ]}
       {[ "Empty"%cpp_name := Gstruct zero_global_struct ]}
       ∅ [] [] abi.abi_default ∅ ∅ ∅ ∅;
     member_pointer_bitsize := bitsize.W64 |}.

Definition skip_function : Func :=
  Build_Func Tvoid [] CC_C Ar_Definite exception_spec.Unknown (Some (Impl Sskip)).

Section with_logic.
  Context `{Σ : cpp_logic}.

  Lemma zero_symbol_benign ty :
    size_of (global_size_env ty) ty = Some 0%N ->
    emp |-- denoteSymbol (σ := global_size_env ty) (global_size_env ty).(genv_tu)
      "object"%cpp_name (Ovar ty global_init.NoInit).
  Proof.
    intros Hsize. by rewrite /denoteSymbol Hsize bool_decide_true // _at_emp.
  Qed.

  Lemma zero_module_benign ty :
    size_of (global_size_env ty) ty = Some 0%N ->
    emp |-- denoteModule (σ := global_size_env ty) (global_size_env ty).(genv_tu).
  Proof.
    intros Hsize.
    have Hlist : map_to_list (global_size_env ty).(genv_tu).(symbols) =
      [("object"%cpp_name, Ovar ty global_init.NoInit)].
    { vm_compute. reflexivity. }
    rewrite denoteModule_eq /denoteModule_def Hlist big_sepL_singleton /=.
    iIntros "H". iSplitL.
    { by iApply zero_symbol_benign. }
    iPureIntro.
    case E: (module_le (global_size_env ty).(genv_tu) (global_size_env ty).(genv_tu)); first done.
    have Hbad := module_le_sound (global_size_env ty).(genv_tu) (global_size_env ty).(genv_tu).
    rewrite E in Hbad. exfalso. apply Hbad. reflexivity.
  Qed.

  Lemma zero_function_blocked ty f args Q :
    size_of (global_size_env ty) ty = Some 0%N ->
    wp_func (σ := global_size_env ty) (global_size_env ty).(genv_tu) f args Q |-- False.
  Proof.
    intros Hsize. iIntros "H".
    iDestruct (observe [| function_admitted (global_size_env ty).(genv_tu) |] with "H") as %[Hcompat Had].
    have Hnz := Had "object"%cpp_name (Ovar ty global_init.NoInit) ltac:(vm_compute; reflexivity).
    rewrite /global_size_admitted Hsize in Hnz.
    exfalso. by apply Hnz.
  Qed.

  Example zero_array_function_blocked f args Q :
    wp_func (σ := global_size_env "unsigned char[0]"%cpp_type)
      (global_size_env "unsigned char[0]"%cpp_type).(genv_tu) f args Q |-- False.
  Proof. apply zero_function_blocked. reflexivity. Qed.

  Example zero_named_function_blocked f args Q :
    wp_func (σ := global_size_env "Empty"%cpp_type)
      (global_size_env "Empty"%cpp_type).(genv_tu) f args Q |-- False.
  Proof. apply zero_function_blocked. reflexivity. Qed.

  Example zero_qualified_function_blocked f args Q :
    wp_func (σ := global_size_env "const Empty"%cpp_type)
      (global_size_env "const Empty"%cpp_type).(genv_tu) f args Q |-- False.
  Proof. apply zero_function_blocked. reflexivity. Qed.

  Lemma old_module_contradiction :
    denoteModule (σ := global_size_env "Empty"%cpp_type)
      (global_size_env "Empty"%cpp_type).(genv_tu) |-- False.
  Proof.
    iIntros "M".
    Fail solve [
      iDestruct (observe [| size_of (global_size_env "Empty"%cpp_type) "Empty"%cpp_type <> Some 0%N |]
        with "M") as "%H";
      exfalso; apply H; reflexivity].
  Abort.

  (* The old rule cannot omit its new semantic admission premise. *)
  Fail Definition unchecked_global_rule (σ : genv) tu ρ ty x Q :
    read_decl (resolve := σ) (_global x) ty (fun p => Q p FreeTemps.id)
    |-- wp_lval tu ρ (Eglobal x ty) Q := expr.E.wp_lval_global tu ρ ty x Q.

  Definition checked_global_rule (σ : genv) tu ρ ty x Q :
    ([| size_of σ ty <> Some 0%N |] **
      read_decl (resolve := σ) (_global x) ty (fun p => Q p FreeTemps.id))
    |-- wp_lval tu ρ (Eglobal x ty) Q := expr.E.wp_lval_global tu ρ ty x Q.

  Lemma admitted_skip_function (σ : genv) tu :
    function_admitted (σ := σ) tu ->
    emp |-- wp_func (σ := σ) tu skip_function [] (fun _ => True%I).
  Proof.
    intros Had. iIntros "_". iApply (wp_func_intro (σ := σ) tu skip_function [] (fun _ => True%I)). cbn.
    iSplit; first by iPureIntro.
    iNext. iApply wp_seq. rewrite wp_block_eq /wp_block_def /=.
    iModIntro. iNext. iModIntro.
    rewrite /Kcleanup /Kat_exit /Kreturn /Kreturn_inner /=.
    iIntros (?) "_". done.
  Qed.

  Lemma self_globals_admitted ty :
    size_of (global_size_env ty) ty <> Some 0%N ->
    function_admitted (σ := global_size_env ty) (global_size_env ty).(genv_tu).
  Proof.
    intros Had. split; first by constructor.
    intros n o Hlookup.
    destruct (TM.map_to_list_elements n o _ Hlookup) as [xs [ys Hlist]].
    have Hin : In (n, o) (map_to_list (global_size_env ty).(genv_tu).(symbols)).
    { rewrite Hlist. apply in_or_app. right. by left. }
    have Hsingle : map_to_list (global_size_env ty).(genv_tu).(symbols) =
      [("object"%cpp_name, Ovar ty global_init.NoInit)] by vm_compute; reflexivity.
    rewrite Hsingle in Hin. destruct Hin as [Heq|[]].
    injection Heq as Hnm Ho. subst n o. exact Had.
  Qed.

  Example ordinary_function_supported :
    emp |-- wp_func (σ := global_size_env "int"%cpp_type)
      (global_size_env "int"%cpp_type).(genv_tu) skip_function [] (fun _ => True%I).
  Proof. apply admitted_skip_function, self_globals_admitted. discriminate. Qed.

  Example incomplete_type_function_supported :
    emp |-- wp_func (σ := global_size_env "Forward"%cpp_type)
      (global_size_env "Forward"%cpp_type).(genv_tu) skip_function [] (fun _ => True%I).
  Proof. apply admitted_skip_function, self_globals_admitted. discriminate. Qed.

  (* An abstract resolver can complete an extern type with zero size. Its
     admission is a real client premise, not a fact extracted from modules. *)
  Example abstract_resolver_function_supported (σ : genv) tu :
    function_admitted (σ := σ) tu ->
    emp |-- wp_func (σ := σ) tu skip_function [] (fun _ => True%I).
  Proof. apply admitted_skip_function. Qed.
End with_logic.

(* Global address injectivity remains a contract for admitted programs. *)
Example global_address_identity σ tu :
  Inj (=) (=) (fun n => @ptr_vaddr σ (global_ptr tu n)).
Proof. apply _. Qed.
