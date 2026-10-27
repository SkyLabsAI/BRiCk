(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.prelude.base.
Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import skylabs.lang.cpp.logic.
Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.

(** * Function attributes ([fn_attr.t])

cpp2v records <<noreturn>>, <<nonnull>> and <<returns_nonnull>> in
[f_attrs]/[m_attrs]; [wp_func]/[wp_method] enforce them. *)

cpp.prog source flags "-std=c++20 --target=x86_64-linux-gnu" prog cpp:{{
[[noreturn]] void nr_decl();
__attribute__((noreturn)) void nr_def() { for (;;) {} }
_Noreturn void nr_c11();
void plain(int *p);
void nn_one(int *p, int *q) __attribute__((nonnull(1)));
void nn_two(int *p, int x, int *q) __attribute__((nonnull(1, 3)));
__attribute__((nonnull)) void nn_all(int *p, int x, char *q, int &r);
void nn_param(int x, int *__attribute__((nonnull)) p);
__attribute__((returns_nonnull)) int *rnn();
[[noreturn]] __attribute__((nonnull, returns_nonnull)) int *everything(int *p);
struct S {
  [[noreturn]] void nr();
  void nn(int x, int *__attribute__((nonnull)) p);
  __attribute__((returns_nonnull)) S *self() { return this; }
  static void snn(int *p) __attribute__((nonnull(1)));
};
}}.

Definition fn_attrs_of (n : name) : option (list fn_attr.t) :=
  match source.(symbols) !! n with
  | Some (Ofunction f) => Some f.(f_attrs)
  | Some (Omethod m) => Some m.(m_attrs)
  | _ => None
  end.

Example noreturn_spellings :
  fn_attrs_of <$> ["nr_decl()"; "nr_def()"; "nr_c11()"]%cpp_name =
  replicate 3 (Some [fn_attr.Noreturn]).
Proof. vm_compute. reflexivity. Qed.

Example no_attributes :
  fn_attrs_of "plain(int*)"%cpp_name = Some [].
Proof. vm_compute. reflexivity. Qed.

(* Indices are 0-based; the argument-less spelling covers pointer
   parameters only, not [int] or references. *)
Example nonnull_indices :
  fn_attrs_of <$>
    ["nn_one(int*, int*)"; "nn_two(int*, int, int*)";
     "nn_all(int*, int, char*, int&)"; "nn_param(int, int*)"]%cpp_name =
  Some <$> [[fn_attr.Nonnull [0]]; [fn_attr.Nonnull [0; 2]];
            [fn_attr.Nonnull [0; 2]]; [fn_attr.Nonnull [1]]]%N.
Proof. vm_compute. reflexivity. Qed.

Example returns_nonnull :
  fn_attrs_of "rnn()"%cpp_name = Some [fn_attr.Returns_nonnull].
Proof. vm_compute. reflexivity. Qed.

Example all_three :
  fn_attrs_of "everything(int*)"%cpp_name =
  Some [fn_attr.Noreturn; fn_attr.Nonnull [0]; fn_attr.Returns_nonnull]%N.
Proof. vm_compute. reflexivity. Qed.

(* Method parameter indices exclude [this]. *)
Example method_attributes :
  fn_attrs_of <$> ["S::nr()"; "S::nn(int, int*)"; "S::self()"; "S::snn(int*)"]%cpp_name =
  Some <$> [[fn_attr.Noreturn]; [fn_attr.Nonnull [1]];
            [fn_attr.Returns_nonnull]; [fn_attr.Nonnull [0]]]%N.
Proof. vm_compute. reflexivity. Qed.

(** ** Enforcement *)
Section enforcement.
  Context `{Σ : cpp_logic} {σ : genv} (tu : translation_unit).

  (* A function without attributes has the same [wp_func] as before. *)
  Example wp_func_no_attrs (f : Func) body args Q :
    f.(f_attrs) = [] ->
    f.(f_body) = Some (Impl body) ->
    wp_func tu f args Q =
      (let ρ vap := Remp None vap f.(f_return) in
       letI* ρ, cleanup := bind_vars tu f.(f_arity) f.(f_params) args ρ in
       |> wp tu ρ body (Kcleanup tu cleanup $ Kreturn $ fun x => |={top}=> |> Q x))%I.
  Proof. intros Ha Hb. rewrite wp_func.unlock /= Hb Ha /=. reflexivity. Qed.

  (* A <<noreturn>> function may not return normally. *)
  Example wp_func_noreturn (f : Func) body args Q :
    f.(f_attrs) = [fn_attr.Noreturn] ->
    f.(f_body) = Some (Impl body) ->
    wp_func tu f args Q =
      (let ρ vap := Remp None vap f.(f_return) in
       letI* ρ, cleanup := bind_vars tu f.(f_arity) f.(f_params) args ρ in
       |> wp tu ρ body (Kcleanup tu cleanup Knoreturn))%I.
  Proof. intros Ha Hb. rewrite wp_func.unlock /= Hb Ha /=. reflexivity. Qed.

  (* A <<noreturn>> function without <<nonnull>> gets no obligation, and the
     body is reached without any hint. *)
  Example wp_func_noreturn_no_obligation (f : Func) body args Q :
    f.(f_attrs) = [fn_attr.Noreturn] ->
    f.(f_params) = [] ->
    f.(f_body) = Some (Impl body) ->
    wp_func tu f args Q =
      (let ρ vap := Remp None vap f.(f_return) in
       letI* ρ, cleanup := bind_vars tu f.(f_arity) [] args ρ in
       |> wp tu ρ body (Kcleanup tu cleanup Knoreturn))%I.
  Proof. intros Ha Hp Hb. rewrite wp_func.unlock /= Hb Ha Hp /=. reflexivity. Qed.

  Example Knoreturn_blocks_return rt : Knoreturn rt |-- False.
  Proof. apply Knoreturn_elim. Qed.

  (* A <<nonnull>> parameter leaves a [with_nonnull_params] obligation that
     does not reduce (its lookup goes through [N.to_nat]); automation
     resolves it by computing [nonnull_ptrs]. *)
  Example wp_func_nonnull (f : Func) body (p q : ptr) Q :
    f.(f_attrs) = [fn_attr.Nonnull [1]]%N ->
    f.(f_body) = Some (Impl body) ->
    wp_func tu f [p; q] Q =
      with_nonnull_params [1]%N f.(f_params) [p; q]
        (let ρ vap := Remp None vap f.(f_return) in
         letI* ρ, cleanup := bind_vars tu f.(f_arity) f.(f_params) [p; q] ρ in
         |> wp tu ρ body (Kcleanup tu cleanup $ Kreturn $ fun x => |={top}=> |> Q x))%I.
  Proof. intros Ha Hb. rewrite wp_func.unlock /= Hb Ha /=. reflexivity. Qed.

  Example nonnull_ptrs_computes (p q : ptr) :
    nonnull_ptrs [("p"%pstring, Tptr Tint); ("q"%pstring, Tqualified QC (Tptr Tint))] [p; q] [1]%N
    = Some [(Tqualified QC (Tptr Tint), q)].
  Proof. vm_compute. reflexivity. Qed.

  Example nonnull_ptrs_missing (p : ptr) :
    nonnull_ptrs [("p"%pstring, Tptr Tint)] [p] [3]%N = None.
  Proof. vm_compute. reflexivity. Qed.

  (* The observation is satisfied by an argument object holding a non-null
     pointer, and costs the body nothing. *)
  Example nonnull_ob_intro (p v : ptr) (P : mpred) :
    v <> nullptr ->
    p |-> primR (Tptr Tint) 1$m (Vptr v) ** P |-- (nonnull_ob (Tptr Tint, p) ∧ (p |-> primR (Tptr Tint) 1$m (Vptr v) ** P))%I.
  Proof.
    intros. iIntros "H". iSplit; last done.
    iDestruct "H" as "[P _]". iExists _. by iFrame.
  Qed.
End enforcement.
