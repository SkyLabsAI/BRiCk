The Spectra Framework
==

Contributions
===
- v1 (2020) developed by Gregory Malecha and Jonas Kastberg Hinrichsen.
- v2 (2021) complete rewrite by Gordon Stewart and Gregory Malecha based on ideas of v1 
  to support set refinement and to re-formulate requesters and committers in terms of 
  Iris atomic updates.
- Further contributions by Abhishek Anand, Paolo G. Giarrusso, Yoichi Hirai,
  Hoang-Hai Dang, incluing generalization to n-ary composition and
  BI-polymorphism.

High-level Idea
===
This framework can be used to reason about implementations that
refine operational models expressed as labeled transition systems (LTS).
The framework provides an idiomatic way to express the state of the
specification within separation logic.

Beyond the embedding of the state into separation logic, this framework
provides a modular way to reason about pairs of these LTSs when they
communicate. In particular, the abstractions in this library allow for
reasoning about the behavior of an LTS **independent** of the states
of other LTSs that are communicating with it.

In addition, the framework provides separation logic analogs for
various process-calculi operators, e.g. parallel composition and hiding,
which allow users to decompose a large LTS into its smaller constituent
pieces, distribute them to various parts of the implementation using
fictional separation, and ultimately build the refinement modularly.

Consider a simple LTS which is built from the parallel composition of
four smaller LTSs:

    root := (A || B) || (C || D)

This framework allows us to prove that an implementation refines this
specification in a modular way. 

The Abstraction
====

The framework encapsulates the exact way that this refinement is performed
and instead exposes abstract ghost state to reason about the model.

The current state of the system is expressed through the predicate
`AuthSet.frag γlts states` where `states` is a (guaranteed nonempty) set
of possible states of the LTS. Using a set of states rather than a single
state allows for a simpler formulation of more sophisticated refinements.

The framework also exposes means of updating this state when the underlying
LTS can take a step.

Updaters
=====
Updaters allow taking silent ($\tau$) steps that are allowed by the
specification.

```coq
Definition updater (E : coPset) γ : PROP :=
  □ ∀ (sset : propset root.(lts_state))
      (_ : ∃ s, s ∈ sset)
      (_ : tau_safe root sset),
      AuthSet.frag γ sset ={E}=∗
      AuthSet.frag γ {[ s' | ∃ s, s ∈ sset ∧ root.(lts_step) s None s' ]}.
```

Requesters and Committers
=====

Communication, i.e. non-$\tau$ events, are divided into two sides: requesters
(`Step.requester`) and committers (`Step.committer`). At the process calculus
level, both parties are enabled on dual events and can simultaneously step
cancelling the events into a single $\tau$ event. At the implementation level,
one party requests one of a set of events and the committer which commits to
one event from the set. The use of the event set on the request side allows
modeling common idioms where one party issues a read with an unconstrained value
and the other party is enabled on the event that reads the correct value.

The crucial feature of `Step.requester` and `Step.committer` is that they are
completely local, only mentioning a single party. This allows performing modular
code verification while being ambivalent on other parties within the system.

Decomposition
====

The main theorems in the framework establish separation logic-level
reasoning principles for process calculus operators. The main
decomposition theorem is about parallel composition and effectively describes
how an `AuthSet.frag γAB (A,B)`, where `(A,B)` is the state of the
LTS `A || B`, can be decomposed into an 
`AuthSet.frag γA A ** AuthSet.frag γB B` and how requesters, committers,
and updaters can be transported along this decomposition, e.g.
that an updater for `A` can be established from the updater for `A || B`.

Thanks to the uniformity of the composed and decomposed system (both follow the
setup of the framework), this theorem can be applied repeatedly
to decompose larger systems into their constituent pieces and can be
interleaved with other theorems in the framework to reason about other
process calculus operators.

Idiomatic Usage
===

`Step.requester` and `Step.committer` are defined using ACs/AUs respectively that
include as preconditions of an app's external functions, e.g.:
```coq
(* requester spec: *)
\with Q
\pre Step.requester γr STEPr Q
\post
  Exists ev, [| ev ∈ STEPr |] ** Q ev
function_called_by_requester_and_proved_by_committer();

(* committer spec *)
\with Q
\pre Step.committer γc STEPc Q
\post
  Exists ev, [| ev ∈ STEPc |] ** Q ev
function_called_by_requester_and_proved_by_committer();
```
`STEPr` is the set of events that the `requester` can discharge
by making the function call.  This is in the setting in which
`requester` and `committer` are independent apps, each
individually proved to refine a distinct operational model.

`requester` is the party making calls. The requester AC defines
how the requester's LTS gets updated as a result of the call but
says nothing about how the `committer`'s state is updated.

`committer` is the party that implements the call. The
`committer` AU describes how the the `committer`'s LTS state is
updated as a result of being called.

For dual event sets (the notion of what is "dual" is defined at
composition time), the `requester` AC implies the `committer`
AU. Because of contravariance, this implication gives that the
committer spec above implies the requester spec
above. Committers (parties implementing an app interface) can
prove `committer spec`. Requesters can use `decompose` to
translate to `requester_spec`.


Adequacy
===

To **formally** prove that the implementation refines the specification,
it is necessary to connect this framework ghost state to the
operational model of the implementation. This is achieved once at the root
invariant and the reasoning principles of the framework allow
ignoring this connection at all other levels. The crucial part in the
connection is to tie the external events of the root LTS to the observable
behaviors of the implementation system. If we assume that the underlying
operational model of the implementation exposes a piece of ghost state
that tracks the visible events of the impementation (call it `trace`),
then we can bind this with the operational model from this framework
using an invariant such as:

```coq
inv "refinement" (
  ∃ root_set init_st evts,
    AuthSet.auth γroot root_set **
    trace evts **
    [| ∃ s, s ∈ root_set |] ** (*<-- cf. [NOTE: tau_safe]*)
    [| root.(lts).(Sts._init_state) init_st |] **
    [| ∀ s, s ∈ root_set -> reachable root.(lts) init_st evts s |])
```

Using the adequacy of Iris and the implementation logic, we can prove from this
invariant that all traces of the implementation are permitted by the specification
(up to stuttering in the implementation).
