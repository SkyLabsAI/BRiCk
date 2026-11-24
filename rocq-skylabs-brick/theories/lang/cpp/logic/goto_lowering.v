(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** * The trusted rule for lowered <<goto>>s (SkyLabsAI/BRiCk#515, sketch)

[Sgoto] and [Slabeled] have no [wp] rule, so the rule below cannot be proved:
it is an axiom about the (unformalized) semantics of <<goto>>.

What is trusted: for every function body [body] that [lower_goto] accepts,
executing [body] from its start, in any region [ρ] whose return type is the
function's, with the continuation of a function body
([Kcleanup tu cl (Kreturn cv Q)], see [wp_func] and [wp_method] in func.v),
refines executing [lower_goto]'s output. That is, C++'s <<goto>> (jump to the
label, leaving the scopes in between, https://eel.is/c++draft/stmt.jump#general-2,
https://eel.is/c++draft/stmt.goto) behaves on accepted bodies like the copy of
the terminal suffix; the comment of ../syntax/goto_lowering.v gives the
argument, condition by condition.

The continuation is fixed because one widening depends on it: for <<void>>
functions, the copy ends with an inserted <<return;>> where the original falls
off the end, and [Kreturn_inner] (with [Kcleanup], [Kfree], [Kseq], [Kloop],
[Kswitch] on the way out) treats [ReturnVoid] like [Normal] at the function
boundary, not in general.

Nothing else is trusted: [lower_goto] is ordinary Gallina, its result is
computed, and it never contains [Sgoto] or [Slabeled].
*)

Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.syntax.goto_lowering.
Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.lang.cpp.logic.pred.
Require Import skylabs.lang.cpp.logic.wp.
Require Import skylabs.lang.cpp.logic.func.

Module Type GOTO_LOWERING.
  Section with_resolver.
    Context `{Σ : cpp_logic} {σ : genv}.

    Axiom wp_lower_goto : forall tu ρ body body' cl cv (Q : ptr -> mpred),
        goto_lowering.lower_goto (get_return_type ρ) body = Some body' ->
            wp tu ρ body' (Kcleanup tu cl (Kreturn cv Q))
        |-- wp tu ρ body (Kcleanup tu cl (Kreturn cv Q)).
  End with_resolver.
End GOTO_LOWERING.

Declare Module goto_rule : GOTO_LOWERING.
Export goto_rule.
