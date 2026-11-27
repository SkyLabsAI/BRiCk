# Classes with virtual functions and virtual bases: design note

*Written by Claude (Claude Code), working with Paolo. Design only: nothing here changes a rule.*

SkyLabsAI/BRiCk#487 (with SkyLabsAI/auto#703) supports classes with virtual bases. It now also
carries the conversions to non-virtual bases (from #545) and to virtual bases (from #549: the
`Cderived2vbase` cast and the `vptrR` token). All of its rules require `tu_no_vtables`: no class
in the hierarchy may have a virtual function.

This note proposes how to lift that restriction. It covers:

- what object identity (`mdc_path`) must mean when a virtual base is shared;
- the dynamic type during construction and destruction;
- final overriders reached through a virtual base;
- how `vptrR` and `mdc_path` fit into one ownership story;
- the changes to #487's rules and to `vstruct_layout_ok`;
- candidate encodings with their trust cost;
- the gate witnesses the design must refute.

Writing it turned up two gate passes (SkyLabsAI/auto#752) against the `Gstruct` rules for classes *without*
virtual bases (see "Gate passes against the former `Gstruct` rules"). Stage 0, in SkyLabsAI/BRiCk#564 with
SkyLabsAI/auto#756 (merged 2026-11-26), fixes them.

Code references are to branch `claude/virtual-bases` (#487), which is not yet on
`paolo/agent-staging`.

## Summary

- **One token per dynamic subobject.** `vptrR` gains an index, the *dynamic state*: either
  `Unsettled`, or a *dynamic identity* made of three parts:
  - the *phase class*: the class whose constructor or destructor last set the identity;
  - a pointer to that class's subobject;
  - the path from it to this subobject.

  Conversions to a virtual base use a fraction of the token in either state, as #487 now does.
  Virtual dispatch needs a settled identity. `mdc_path` becomes a definition over the token.
- **A path has at most one virtual step, and that step comes first.** #487's `VStruct` lays out
  every virtual base relative to the complete object (`vs_vbases`). So a subobject is named by an
  optional virtual base of the phase class, followed by non-virtual steps. Each subobject then has
  exactly one name.
- **Every constructor sets the identity of all its dynamic subobjects, including its virtual
  bases**, not only the most-derived class's. This is what the Itanium ABI's construction vtables
  do, and what [class.cdtor]/4 requires.
- **Constructors.** Between the end of a subobject's constructor and the point where the enclosing
  constructor writes the vptrs, the subobject's state is `Unsettled`. In that window clang may
  already have written the enclosing class's vptrs and gcc has not (witness 9). The call is
  undefined there ([class.base.init]/18), so dispatch must be stuck.
- **Destructors** set the phase of one base subtree right before that base's destructor. The
  `Gstruct` rule reverted all bases at once, which compiled code refutes (candidate B); stage 0
  (SkyLabsAI/BRiCk#564) makes it per base.
- **Dispatch searches the whole hierarchy of the phase class** for the final overrider. It is
  not limited to the classes on the path. The overrider's `this` is the overrider's subobject of the
  phase object. It is reached through `vbase_ptr` when that subobject lies in a virtual base (a
  virtual thunk).
- **Vptr sharing with a virtual base** (a nearly-empty primary virtual base) is accepted only
  when every class whose constructor writes the shared slot contains all the subobjects that share
  it. Otherwise the layout is rejected: clang and gcc miscompile a *defined* conversion in the
  rejected case (witness 7).
- **The motivating client needs less.** In libstdc++, the only virtual functions of `ios_base`,
  `basic_ios` and the stream classes are their destructors. Constructing and destroying
  `std::ostringstream` objects, and converting to `basic_ios`, need the identity bookkeeping
  (stage 1). They do not need dispatch through a virtual base. Even stage 1 needs `mdc_path` to be
  a definition over `vptrR`, because `basic_ios` and `ios_base` are polymorphic classes without
  virtual bases.

## What C++ requires

All references are to the current working draft at eel.is.

- **One shared subobject.** [[class.mi]/4](https://eel.is/c++draft/class.mi#4): for each distinct
  virtual base, "the most derived object shall contain a single base class subobject of that type".
- **Initialization order.**
  - [[class.base.init]/15](https://eel.is/c++draft/class.base.init#15): virtual bases are
    initialized "First, and only for the constructor of the most derived class", then the direct
    bases, then the members, then the body.
  - [[class.base.init]/7](https://eel.is/c++draft/class.base.init#7): a mem-initializer for a
    virtual base "is ignored during execution of a constructor of any class that is not the most
    derived class".
  - `func.v` still cites the order rule as `class.base.init#13`; the draft has renumbered it.
- **Early calls.** [[class.base.init]/18](https://eel.is/c++draft/class.base.init#18): calling a
  member function, including a virtual one, from a mem-initializer before all the mem-initializers
  for base classes have completed is undefined.
- **Destruction order.** [[class.dtor]/13](https://eel.is/c++draft/class.dtor#13): members,
  then non-virtual direct bases, and, if the class is the most derived, "its destructor calls the
  destructors for X's virtual base classes".
- **Final overrider.**
  - [[class.virtual]/2](https://eel.is/c++draft/class.virtual#2): a virtual function of a
    subobject "is a final overrider unless the most derived class" of which it is a subobject has
    another overrider.
  - "if a virtual member function of a base class subobject has more than one final overrider,
    the program is ill-formed".
- **Covariant returns.** [[class.virtual]/9](https://eel.is/c++draft/class.virtual#9): the
  overrider's result "is converted to the type returned by the (statically chosen) overridden
  function".
- **Dynamic type.** [[defns.dynamic.type]](https://eel.is/c++draft/defns.dynamic.type): the "type of
  the most derived object to which the glvalue refers".
- **During construction and destruction.**
  - [[class.cdtor]/4](https://eel.is/c++draft/class.cdtor#4): a virtual call on the object under
    construction or destruction calls "the final overrider in the constructor's or destructor's
    class". A call through a subobject outside that class is undefined.
  - [class.cdtor]/5 and /6 give the same rule for `typeid` and `dynamic_cast`.
  - [[class.cdtor]/3](https://eel.is/c++draft/class.cdtor#3): converting a pointer to class `X`
    into a pointer to a base `B` is defined once the construction of `X`, and of its bases that
    derive from `B`, has started, and until their destruction completes. Otherwise "the conversion
    results in undefined behavior".
- **Outside lifetime.** [[basic.life]/7.3](https://eel.is/c++draft/basic.life#7.3): converting a
  pointer to an object outside its lifetime "to a pointer to a virtual base class" is undefined.
  [basic.life]/8.3 says the same for references.

The gate counts what compiled code does, undefined or not. So wherever the standard leaves a
call undefined, the rules must either agree with every compiler or get stuck.

## What compilers do (Itanium C++ ABI)

The following was observed with clang 22.1.8 and g++ 14.2.0 in the `fm-default` container,
x86-64, at `-O0` and `-O2`. The probes are kept outside the repositories, in
`agent-workspaces/vbase-vfuns-design-probes/`.

- **One vptr slot per dynamic subobject.** A class shares its slot with its *primary base*: the
  first non-virtual dynamic base or, failing that, a nearly-empty virtual base (one holding only a
  vptr). Each slot points into a vtable that holds:
  - the offset to the top of the object, and the RTTI pointer;
  - one offset per virtual base (used by `Cderived2vbase`);
  - function pointers;
  - in the secondary vtables of virtual bases, one *vcall offset* per virtual function whose
    overrider may sit in another subobject.
- **Construction vtables.** A base-object constructor of `L` runs inside a larger object. It
  writes the vptrs of *all* of `L`'s dynamic subobjects, including its virtual bases, with an
  "`L`-in-`G`" vtable taken from the VTT. That vtable has `L`'s overriders, `G`'s virtual-base
  offsets, and offsets to the top that lead to the `L` subobject. Destructors write the same
  vtables back.
- **Early writes.** When a base initializer mentions `this`, clang writes the class's own vptrs,
  for all its dynamic subobjects, *before* that initializer runs (`EmitBaseInitializer`,
  `BaseInitializerUsesThis`, in clang's `CGClass.cpp`). gcc writes them only after the last base
  initializer. So in the window between base initializers, a subobject that is already built is in
  the enclosing class's phase under clang and in its own phase under gcc.
- **Destructors with empty bodies.** Clang can skip the vptr writes in a destructor whose body
  does nothing (`CanSkipVTablePointerInitialization`), but not when a member destructor could
  observe the slot. With `B1 { M m; virtual int f(); ~B1() {} }`, where `~M()` calls `f` through
  a pointer to the `B1` subobject of a `C : B1` that overrides `f`, both compilers call `B1::f`.
- **Probe: construction phase.** With `VB { virtual int f() }`, `L : virtual VB` overriding `f`
  to return 1, and `G : L, R` overriding it to return 2, a call through a `VB*` inside `L`'s
  constructor or destructor body returns 1 while a `G` is being built or destroyed. It does not
  return 2 (`G::f`) or 0 (`VB::f`).
- **Probe: virtual thunks.** In `H : L, R`, with only `L` overriding `VB::f`, a call through
  `(VB*)(R*)&h` reaches `L::f`. The thunk reads the vcall offset and adjusts `this` by -40 bytes. In
  a complete `L` the same thunk adjusts by -16. So the adjustment depends on the most-derived
  object, as virtual-base offsets do.

## BRiCk today

- **`mdc_path cls path q p`** (`logic/pred.v`, as a `Rep`: `derivationR`) is fractional ownership
  of the identity of the `cls` subobject at `p`.
  - `path` lists the classes from the most-derived class down to `cls`.
  - `[]` means "not yet initialized". `struct_defR` (`heap_pred/everywhere.v`) includes
    `derivationR cls nil`.
  - Its model is a ghost map keyed by pointer (`derivation_own`, `model/simple_pred.v`).
    `mdc_path_agree` makes the path and the class unique per pointer. `mdc_path_forget` is an
    axiom.
  - Tokens exist only for classes with `has_vtable`. That holds for a class that declares or
    overrides a virtual function, not for one that only inherits virtual functions.
- **`wp_init_identity`** (`func.v`): after *all* base initializers, a constructor consumes the
  bases' tokens, which are in the bases' own phase, and returns tokens for the whole subtree with
  the class prepended. Until then the bases' tokens stay in their own phase.
- **`wp_revert_identity`**: the `Gstruct` case of `wp_dtor` destroys the members, then calls
  `wp_revert_identity` once for all bases, then destroys the bases (`wpd_bases`, in reverse order).
  So while the last base is destroyed, every earlier base is already back in its own phase.
- **`resolve_virtual`** (`logic/dispatch.v`) looks at (`//\\`) the token at `this`.
  - It calls `dispatch` (`semantics/dispatch.v`) on the path. `dispatch` walks *the path only*,
    from the base up to the most-derived class, checking `s_overrides`.
  - It adjusts `this` by `base_to_derived`, which uses static `o_derived` offsets.
  - `dispatch` returns `None` when a class *above* the bottom of the path is not a `Gstruct`. A
    one-element path `[cls]` succeeds without looking at `cls`.
- **`vptrR cls q`** (`heap_pred/vbase.v`, from #549) is ownership of an installed vptr.
  - It is a bare `Parameter` with two axioms (`Timeless`, `CFractional`) and no model in
    `simple_pred.v`.
  - The `Gvstruct` constructor rule creates it after the non-virtual bases, and the destructor
    rule takes it back.
  - `Cderived2vbase` borrows a fraction of it, together with the persistent `vbase_ptr`.
  - It fixed two gate witnesses, `vbase_vptr_early` and `vbase_stale_reuse` (auto's
    `fixed_regression_tests`, now in SkyLabsAI/auto#703).
- **Covariant returns.** `dispatch` (`logic/expr.v`) calls the overrider at the statically chosen
  function type, and nothing in it converts the result.

So BRiCk has two tokens for one machine word: `mdc_path` for dispatch and `vptrR` for casts.
Neither knows about the other, and the rules that update `mdc_path` stop at the first class with
virtual bases.

## Prior art: brick-lean

[SkyLabsAI/brick-lean](https://github.com/SkyLabsAI/brick-lean) ports BRiCk to Lean and proves its
rules against an operational machine. Read at commit `64731e5` (2026-11-27).

**What it does not cover.** Classes with virtual bases are modelled for layout only. Construction,
conversions to a virtual base, and dispatch through one are refused (`docs/FEATURES.md`,
`docs/MODEL.md`). So construction vtables, phases, thunks and vptr sharing are as open there as
here.

**What it does settle:**

- **A model for `vbase_ptr`** (`BRiCk/Model/MemInterp.lean`). Pointers there are an allocation plus
  a path. `vbase_ptr cls vb p pvb` means `pvb = vbaseLoc cls vb p`:
  - `vbaseLoc` strips the base and derived steps of `p`'s path back to the enclosing complete
    object (`anchor`);
  - it then appends one virtual-base step.

  Two laws are proved there, not assumed:
  - `vbaseLoc_base`: going down through a non-virtual base keeps the same complete object. This is
    the law whose absence is #549's spec burden; BRiCk only has `vbase_facts_down` inside rules.
  - `vbaseLoc_vbase`: a virtual base's own virtual bases are relative to the same complete object.

  This is §1's canonical path, and it gives §3 a third option for where `vbase_ptr` comes from.
- **An aliasing pitfall.** The virtual step is encoded with the same segment constructor as a
  non-virtual base step. So in `Both : VB, L` with `L : virtual VB`, the two `VB` subobjects would
  get the same path, and brick-lean refuses such classes (`Examples/VirtualBasesReviewTest.lean`).
  §1's `vpath` keeps the virtual step in a field of its own for this reason.
- **A model for the identity token.** `mdc_path` is a per-pointer ghost map (`γident`), matched to a
  machine field (`MState.idents`). The identity updates are machine steps (`docs/CLASSES.md` §7).
  Storing §1's `dyn_state` there instead of a path is the model §4 asks for.
- **Pure virtual functions** (`docs/CLASSES.md`, list item 12; brick-lean's issue bk49 against
  BRiCk's `resolve_virtual`). BRiCk's `tu_dispatch` never reads purity, so the rule calls the
  definition of a pure function. brick-lean's `final_overrider` drops pure targets. Purity is read
  from the class that declares the overrider, which may redeclare as pure what its base defines.
- **Covariant returns** (item 14). The rule calls the overrider at the type the call names. No spec
  of the overrider matches that type, so the call is stuck. It is a gap in support, not in
  soundness.
- **Candidate A was already on record** (item 13, from a Codex review of 2026-11-13): a call through
  a sibling base during construction, `SD(int*) : SB(this, out)`, where the machine gives 1 and Clang
  gives 7. It stayed a known hole. brick-lean's adequacy theorem is relative to its own machine,
  which follows the logic there, so the theorem never refuted the rule. brick-lean's destructors
  also revert all bases in one step after the fields, as BRiCk did before stage 0. So candidate B
  presumably applies there too; this was not run.

## 1. What `mdc_path` must mean when a virtual base is shared

With `struct G : L, R` and `L, R : virtual VB`, the one `VB` subobject is reached along both
`[G; L; VB]` and `[G; R; VB]`. `mdc_path_agree` allows only one path per pointer, so the path must
be canonical. Two candidates:

- **First path in declaration order** (`[G; L; VB]`). This is arbitrary, and it leaks the order
  of the bases into specs. It also misleads, because dispatch from `VB` must not be limited to `L`
  (§3).
- **A virtual step straight from the top** (recommended). #487's `VStruct` lists the virtual bases
  of a complete object with offsets in the complete object (`vs_vbases`), so a subobject is
  ```
  Record vpath := { vp_vbase : option globname ; vp_nv : list globname }.
  ```
  that is, optionally a virtual base of the top class, then non-virtual steps. `VB` in `G` is
  `{| vp_vbase := Some VB; vp_nv := [] |}`. [class.mi]/4 makes this name unique. The virtual step
  needs a field of its own: if it were encoded like a non-virtual step, `Both : VB, L` with
  `L : virtual VB` would give both `VB` subobjects the same name, which is why brick-lean refuses
  such classes ("Prior art"). brick-lean's `vbaseLoc` has the same shape otherwise. #487 already
  prints a conversion through a virtual base as one `Cderived2vbase` step to the virtual base,
  followed by ordinary `Cderived2base` steps. Clang's cast paths have the same shape.

Since [class.virtual]/2 makes the final overrider unique, the path does not choose the function;
it only names the subobject. Dispatch needs three things:

- (a) the class whose overriders apply;
- (b) a pointer to that class's subobject;
- (c) where the subobject sits inside it.

The current `mdc_path` has (a) and (c), and recovers (b) through static `o_derived` offsets. Those
offsets do not exist across a virtual step: `static_cast` from a virtual base to a derived class is
ill-formed. So the state must carry (b):

```
Record dyn_id := { di_phase : globname ; di_top : ptr ; di_path : vpath }.
Inductive dyn_state := Unsettled | Settled (id : dyn_id).
```

`di_phase` is the most-derived class once the object is fully constructed. Otherwise it is the
class whose constructor or destructor last set the identity. `di_top` is the `di_phase`
subobject; it is also what `dynamic_cast<void*>` must return, since construction vtables measure
the offset to the top from it ([class.cdtor]/6, SkyLabsAI/BRiCk#511).

## 2. Construction vtables: the dynamic type during construction

By [class.cdtor]/4, while `L`'s constructor runs as part of a `G`, every subobject of `L` behaves
as if the object were an `L`. That includes the virtual base `VB`, which `L` did not construct.
Two simplifications are tempting, and both are wrong:

- **Only the most-derived constructor updates virtual bases** (mirroring #487's "most-derived
  conditional"). `VB` then stays in phase `VB` during `L`'s body, and a call through `VB*` gives
  `VB::f`. Compiled code gives `L::f` (witness 2).
- **The identity of a virtual base is fixed at layout time**, like `vbase_ptr`. `VB` then has
  phase `G` throughout, and the same call gives `G::f`. The stale and early witnesses (5 and 6)
  also refute this.

**Constructors.** A constructor of class `C` (complete or base mode) handles its dynamic
subobjects in two steps:

1. **When each non-virtual base constructor returns**, the rule takes that base's tokens: the
   base itself, its dynamic subobjects, and its virtual bases (through `vbase_ptr`). It sets them
   to `Unsettled`. The same happens in `wp_init_complete_vstruct` after each virtual base is
   constructed.
2. **At the point where the vptrs are written** (after the non-virtual base initializers, before
   the members), the rule sets every dynamic subobject of the `C` object to
   `Settled {| di_phase := C; di_top := this; di_path := <its path from C> |}`. That covers the
   non-virtual subobjects at static offsets and the virtual ones found through
   `vbase_ptr C VB this pvb`. `C`'s own token is created at this step, as `vptrR` is today.

For `G` with `L, R : virtual VB`, `VB` goes through `Settled` phase `VB` (its own constructor),
then `Unsettled`, then `L`, then `Unsettled`, then `R`, then `Unsettled`, then `G`. The settled
phases are the vtables that the VTT installs. The `Unsettled` windows are where clang's early
writes (or the next constructor's) may already have changed the slot (witness 9).

- **Casts** work in either state. Every vtable a slot can hold in the window has the virtual-base
  offsets of the same complete object, except when slots are shared (§6). So conversions allowed
  by [class.cdtor]/3 keep working.
- **Dispatch** needs `Settled`. Calls in the window are undefined ([class.base.init]/18), and the
  compilers disagree on them, so dispatch must be stuck there.

**Destructors.** Before a destructor calls the destructor of a base subobject `B`, it sets the
identity of `B`'s subtree, including `B`'s virtual bases, to `Settled` phase `B`. `B`'s destructor
consumes `B`'s own token when it returns. The complete-object rule (`wp_destroy_vstruct`) sets each
virtual base to its own phase before destroying it. So between `R`'s destructor and `L`'s, `VB`
moves from phase `R` to phase `L`.

Doing it per base matters. While `B2` is destroyed, both compilers still have `C`'s vtable in the
slot of `B1`, which has not been destroyed yet. The former single revert of the `Gstruct` rules had
already put `B1` back in phase `B1` (candidate B; fixed by SkyLabsAI/BRiCk#564).

**Where the rules agree with compiled code.** Settled tokens describe what every compiler's slot
holds, in the states the rules reach. The [class.cdtor]/4 example (`D : A, B` with
`A, B : virtual V`) calls through a sibling `A*` during `B`'s constructor. That call is undefined:

- with a `V` that holds data, clang calls `D::f` (early write, because `B((A*)this, this)` mentions
  `this`), while gcc calls `A::f`;
- in the rules above, `A`'s token is `Unsettled` there, so the call is stuck.

## 3. Final overriders through a virtual base, and thunks

The final overrider for the subobject at `di_path` in `di_phase` may live in a class that is
*not on the path*. In `H : L, R`, with only `L` overriding `VB::f`, a call through `R`'s `VB`
reaches `L::f`. The current `dispatch` walks the path (`[H; R; VB]`, or `[H; VB]` in canonical
form) and would find `VB::f` (witness 1).

- **Semantic function** (a definition, not an axiom):
  ```
  final_overrider σ (phase : globname) (target : vpath) (fn : obj_name)
    : option (globname * vpath * obj_name)
  ```
  The candidates are the subobjects of `phase` that contain `target`:
  - the classes along `target`'s non-virtual steps;
  - if `target` starts with a virtual step to `VB`, every subobject of `phase` whose class has
    `VB` as a virtual base, together with `phase` itself.

  The result is the unique most-derived overrider of `fn` among them. cpp2v can check that it is
  unique; compilers reject programs where it is not. If that overrider is pure, `final_overrider`
  returns `None`, because the machine calls `__cxa_pure_virtual`. This can happen during
  construction, when the phase class is abstract. Today's `tu_dispatch` ignores purity altogether.
  brick-lean has fixed that, reading purity from the class that declares the overrider ("Prior
  art"), and the fix carries over independently of virtual bases.
- **`this` adjustment.** The overrider's `this` is the location of the overrider's subobject,
  computed from `di_top` and the returned `vpath`. For a virtual first step it is
  `pvb ,, <non-virtual offsets>` with `vbase_ptr phase VB di_top pvb`. This is the virtual thunk;
  the vcall offset is what the vtable caches. In `H` it is -40 bytes from `R`'s `VB`, and in a
  complete `L` it is -16 (witness 4). No static offset gives it.
- **Where the `vbase_ptr` facts come from at a call site:**
  - (i) The rule asks the caller for `vbase_ptr di_phase VB di_top pvb`. This adds no trust and
    matches the casts. It inherits their spec burden: a caller holding only an `R` subobject does
    not have `G`'s facts.
  - (ii) An observation law on the token:
    `vptrR cls (Settled id) q ⊢ ∃ pvb, vbase_ptr id.(di_phase) VB id.(di_top) pvb` for each virtual
    base `VB` of `di_phase`. It holds in the intended model, since the vtable holds those offsets,
    but it is one more axiom.

  - (iii) A pointer model in which the location follows from the pointer itself, as brick-lean's
    `vbaseLoc` ("Prior art"). Then `vbase_ptr` at any subobject, including the transport down
    through non-virtual bases, is a law of the pointer interface with a model, not a rule premise
    or an axiom about the token. With structured pointers, `di_top` may also reduce to the phase
    class plus the path, since the complete object can be read off any subobject pointer. The cost
    is a model change to BRiCk's pointers, plus the interface laws.

  Recommendation: (i) first. Prefer (iii) to (ii) if BRiCk's pointer model can take
  `vbaseLoc`'s shape.
- **Covariant returns through a virtual base** are a *return* thunk: the overrider's result is
  converted with `Cderived2vbase`, which reads the vptr of the *returned* object. The dispatch
  rule must then ask for a fraction of the returned object's `vptrR` (and accept null), exactly as
  `wp_operand_cast_derived2vbase` does (witness 8). `dispatch` does not convert results today, for
  any covariant return; that gap predates virtual bases. brick-lean confirms the call is stuck
  rather than unsound: no spec of the overrider matches the type the call names.

## 4. One ownership story for `vptrR` and `mdc_path`

Both tokens describe the same machine word: the vptr selects both the virtual-base offsets (casts)
and the overriders (dispatch). With two independent tokens, every rule must update both and nothing
checks that it does. A client can also hold one without the other: with `derivationR` left alone,
a `Gstruct` virtual base such as `basic_ios` keeps the path `[basic_ios]` after the complete object
is built, and the one-element path dispatches (§BRiCk today). Recommended:

```
Parameter vptrR : forall `{cpp_logic} {σ} (cls : globname) (st : dyn_state) (q : cQp.t), Rep.
(* Timeless, CFractional as in #549; agreement and validity as for mdc_path: *)
Axiom vptrR_agree : ...
  Observe2 [| st1 = st2 /\ cls1 = cls2 |] (vptrR cls1 st1 q1) (vptrR cls2 st2 q2).
```

- **Casts** (`Cderived2vbase`) borrow a fraction in any state, as now.
- **Dispatch** borrows a fraction of a `Settled` token and computes from its identity (§3).
- **Ownership flow:**
  - a token is created by its class's constructor when that constructor writes the vptrs (§2);
  - it becomes `Unsettled` when it returns to an enclosing constructor;
  - it is set by that constructor, and by each destructor before it calls the base's destructor;
  - it is consumed by its class's destructor.
- **Never persistent.** Witnesses `vbase_stale_reuse` and `vbase_vptr_early` refute a persistent
  identity for casts, and witnesses 5 and 6 do the same for dispatch.
- **A model.** `vptrR` has none today. Giving it one in `simple_pred.v`, a ghost map keyed by
  pointer like `derivation_own`, turns `vptrR_agree` and the existing instances into theorems.
  Without it, each new instance is an axiom. brick-lean's `γident` is such a map, matched to the
  machine's per-pointer identities, with identity updates as machine steps. Storing a `dyn_state`
  there instead of a path is the model needed.
- **Compatibility.**
  - For hierarchies without virtual bases, `derivationR cls (mdc :: rest) q` becomes a
    *definition* at `p`:
    ```
    vptrR cls (Settled {| di_phase := mdc; di_top := p ,, base_to_derived …;
                          di_path := {| vp_vbase := None; vp_nv := rest |} |}) q
    ```
    Existing client `Rep`s keep their meaning, and `mdc_path` stops being a `Parameter`.
    `mdc_path_forget` needs a counterpart for `vptrR`.
  - The "uninitialized" token `derivationR cls nil`, which `struct_defR` includes, has no
    counterpart in #549, where the token does not exist before the constructor runs. Either
    `dyn_state` gets a third state, "not installed", or `struct_defR` drops the token (see Open
    questions).
- **Which classes get a token.** `has_vtable` is not inherited, but every polymorphic class and
  every class with virtual bases has a vptr. #487 already gives every `Gvstruct` a token. Tokens do
  not have to match slots one-to-one: they are abstract, and agreement with compiled code needs only
  that tokens sharing a slot change together (§6). So stage 1 can keep `has_vtable` for `Gstruct`
  and add every `Gvstruct`.

## 5. Changes to #487's constructor and destructor rules

- **Drop `tu_no_vtables`** from `wp_vstruct_initializer_list` and from the `Gvstruct` case of
  `wp_dtor`.
- **`wpi_nv_bases` and `wpi_bases`.** After each base initializer, take that base's tokens and make
  them `Unsettled` (§2). This applies to the `Gstruct` rules too: the former `wp_init_identity` left
  them in the base's phase (candidate A). Stage 0 does this for `Gstruct` with
  `wp_unsettle_identity` (SkyLabsAI/BRiCk#564).
- **`wp_vstruct_initializer_list`.** Replace `this |-> vptrR cls 1$m -* …` with
  `wp_set_identity tu cls this`. It consumes the tokens of all dynamic subobjects, in any state, and
  returns them settled in phase `cls`.
  - For a virtual base, the rule asks for `∃ pvb, vbase_ptr cls VB this pvb ** pvb |-> <tokens>`
    out of the constructor's own resources. These typically come from `vbaseR` in its
    precondition; `vbase_facts_down` provides the facts in the caller, `wpi_nv_bases`.
  - `wp_init_identity` in the `Gstruct` case becomes the special case without virtual bases.
- **`wp_dtor`, both `Gstruct` and `Gvstruct`.** After the members, and right before each base
  destructor, apply `wp_set_identity tu B (this ,, _base cls B)`. This replaces the single
  `wp_revert_identity` of the `Gstruct` case (candidate B; stage 0 does it for `Gstruct` with
  `wpd_base` and `wp_settle_identity`). At the end, consume
  `this |-> vptrR cls (Settled (phase cls …)) 1$m`, as now.
- **`wp_destroy_vstruct`.** Before each virtual base's destructor, set that virtual base's subtree
  to its own phase.
- **`wp_init_complete_vstruct`.** Each virtual base's own constructor creates its token. The rule
  makes it `Unsettled` afterwards.
- **Specs.**
  - A constructor's postcondition returns its tokens settled in phase `cls` with top `this`. A
    destructor's precondition takes them in that phase.
  - A `Rep` of a class with virtual bases is parameterized by its identity, as `Rep`s mentioning
    `derivationR` are today by their path.
  - `vbaseR cls VB (VBR …)` carries the virtual base's token inside `VBR`, with `di_top` the outer
    object. So a `basic_ios` `Rep` inside an `ostringstream` is parameterized by the
    `ostringstream`'s identity. This is a client cost in stage 1.
- **Unchanged for now:**
  - `delete` stays `UNSUPPORTED`. A virtual destructor through a base pointer needs the
    complete-object pointer (`resolve_complete_obj`), and so a dispatch rule (stage 4).
  - Destroying a named object does not dispatch (`wp_destroy_named`), so the streams' virtual
    destructors need no dispatch for local objects.

## 6. `vstruct_layout_ok` and vptr sharing

#487 rejects any layout where the data of two pieces overlap. That includes a vptr-only virtual
base at offset 0 sharing the vptr of the non-virtual part (`Prim`). With virtual functions this
sharing is common: the Itanium ABI makes a nearly-empty virtual base the primary base when there
is no non-virtual dynamic base. `struct C : virtual I { int x; }`, with `I` holding only a vptr,
puts `I` at offset 0. Clang's record layouts show that whom `I` shares with depends on the
most-derived class:

| Complete class | `I` shares the slot of | Classes writing that slot during construction |
|---|---|---|
| `C : virtual I` | `C` | `I`, then `C` |
| `G1 : C, L` (`L : virtual I { long l; }`) | `C` (and `G1`) | `I`, `C`, **`L`** (does not contain `C`), `G1` |
| `G2 : L, C` | `L` (and `G2`) | `I`, `L`, **`C`** (does not contain `L`), `G2` |

In `G2`, `C`'s base-object constructor writes the "`I`-in-`C`-in-`G2`" vtable into `I`'s slot,
which is `L`'s slot. `L` is fully constructed at that point, so converting a pointer to `L` into an
`I*` is *defined* by [class.cdtor]/3. The compiled code reads a function pointer from the foreign
vtable as if it were a virtual-base offset, and gets garbage (witness 7, both compilers). Tokens
agree with slots only as long as all the subobjects sharing a slot are always updated together.

**Proposed check.** In the data of each piece, separate the vptr slot from the rest, and require:

1. the non-vptr data of all pieces are pairwise disjoint, and disjoint from every vptr slot;
2. two vptr slots are either equal or disjoint;
3. for each slot shared by several subobjects, every class in the hierarchy whose constructor
   writes the slot contains all the live sharers. In practice: the virtual base `I` may share only
   with a subobject `X` such that every class having `I` as a virtual base contains `X`.

`C` passes, and `G1` and `G2` are rejected. The libstdc++ streams do not share (`basic_ios` is not
nearly empty), so stage 1 can keep #487's stricter check and add this later.

## Candidate encodings and their trust cost

Axioms cost most, model changes less, tests least.

| Encoding | What enters the TCB | Verdict |
|---|---|---|
| **A. Two tokens.** Keep `mdc_path` for dispatch (with `vpath`) and `vptrR` for casts; rules update both | `mdc_path`'s index changes (model); new dispatch definitions; each rule updates two tokens, and nothing ties them together | Works, but two `Parameter`s describe one word, specs carry both, and a rule that forgets one is a soundness bug. Stage 1 would also have to consume `derivationR` of `Gstruct` virtual bases, which have no virtual-step path |
| **B. One token `vptrR cls (st : dyn_state)`** (recommended) | `vptrR`'s index; a model for `vptrR` (new, replacing `derivation_own`'s role), so agreement is a theorem; `final_overrider`, `wp_set_identity`, and the new `resolve_virtual` (definitions); changed constructor and destructor rule axioms, `Gstruct` included; optionally one observation axiom (§3 (ii)) | Net fewer `Parameter`s once `mdc_path` becomes a definition. Without a model, agreement is one more axiom |
| **C. One token per complete object**, recording the phase of each subobject | One `Parameter`, but base-mode constructors and destructors need the complete object's token, which their specs do not own | Rejected: breaks modular base-class specs |
| **D. A concrete vptr field**, with vtables as constant data | Vtable layout, offsets, VTTs and thunks become axioms about memory; the ABI enters the TCB | Rejected: largest TCB, ABI-specific, and it would have to model clang's and gcc's different write points |
| **E. Persistent identity**, like `vbase_ptr` | Nothing new | Unsound: witnesses 5 and 6, and #549's two fixed witnesses |

## Witnesses the design must refute

- **Run so far.** Witnesses 1 to 4 were run as probes (see "What compilers do"), and witnesses 7
  and 9 in gate shape.
- **The others are designs**, each aimed at the naive rule named in its row.
- **What each shows.** The program terminates under the gate's observation rules, while the naive
  rule would prove `\post False`.
- **Not yet attempted in Rocq.** None of these has been tried there.

| # | Name | Program | Naive rule refuted | Observed |
|---|---|---|---|---|
| 1 | `vfun_vbase_sibling_dispatch` | `H : L, R`; only `L` overrides `VB::f`; `if (((VB*)(R*)&h)->f() == 0) for(;;);` | `dispatch` extended to `Gvstruct` but still walking the path only (gives `VB::f`) | `L::f` (1), clang/gcc, `-O0`/`-O2` |
| 2 | `vfun_vbase_ctor_phase` | in `L::L()` as a base of `G`: `VB* v = this; if (v->f() != 1) for(;;);` | only the most-derived constructor updates the virtual bases (gives 0), or a virtual base's identity fixed at layout time (gives 2) | 1 |
| 3 | `vfun_vbase_dtor_phase` | the same in `L::~L()` while a `G` is destroyed | `VB` not set to phase `L` before `L`'s destructor (it stays in phase `G` or `R`) | 1 |
| 4 | `vfun_vbase_thunk_this` | `L` overrides `void* who() { return this; }`; `if (((VB*)(R*)&h)->who() != (L*)&h) for(;;);` | `this` adjusted by the offset in a complete `L` (-16, not -40) | equal; offsets -40 in `H`, -16 in `L`. Gate shape needs the logic to decide the pointer comparison; otherwise it is an adequacy test |
| 5 | `vfun_vbase_stale_dispatch` | as `vbase_stale_reuse`, with a virtual call on the dangling pointer after the frame is reused | dispatch with a persistent identity, or with `vbase_ptr` alone | to observe |
| 6 | `vfun_vbase_early_dispatch` | as `vbase_vptr_early`, with a virtual call through an alias of `this` in a base initializer | identity created at layout time instead of when the vptr is written | to observe |
| 7 | `vbase_shared_slot_sibling_ctor` | `I` nearly empty; `L : virtual I`; `C : virtual I` overriding `f`; `G : L, C`; in `C::C()`: `g_i = g_l;` (an `L*` saved by `L::L()`); in `test()`: `if (g_i == (I*)(L*)&g) for(;;);` | any rule faithful to [class.cdtor]/3 on a layout where `I` shares `L`'s slot | `test()` returns: clang `-O0/-O1/-O2` (also with ASan+UBSan), g++ `-O0/-O1/-O2` |
| 8 | `vfun_covariant_vbase_stale` | `Der::get()` returns `Dv*` (with `Dv : virtual VB`) to a destroyed `Dv`; called through `Base::get()` returning `VB*` | the covariant return conversion treated as free (no `vptrR` for the result) | to observe; same mechanism as `vbase_stale_reuse` |
| 9 | `vfun_vbase_early_vptr_write` | `VB` with data; `L : virtual VB` overriding `f` to return 1, saving `g_vb = this` in `L::L()`; `G : L, N` with `G() : N(g_vb->f(), this)`; `if (g.x == 1) for(;;);` | the token of a built base keeps its own phase until the enclosing constructor's vptr write (no `Unsettled`) | `test()` returns with clang `-O0/-O1/-O2` (early write gives `G::f`); g++ loops |

Notes on witness 7:

- Without `C`'s override of `f`, clang keeps the correct answer (the program loops) while g++
  still returns.
- The program never dereferences the garbage pointer, so `test()` returns normally.
- The rows above are compiler behaviour. Whether this is a known Itanium ABI defect, and whether
  to report it upstream, is tracked in SkyLabsAI/BRiCk#562.

### Gate passes against the former `Gstruct` rules

These need no virtual bases. Both programs terminate as described in the `fm-default` container.
Both are gate passes: SkyLabsAI/auto#752 proves `denoteModule source |-- test_post_False` for each
(rows 68 and 69, `tests/unsound/ctor_early_vptr` and `tests/unsound/dtor_revert_identity`). The
merged witnesses keep the mechanisms below but not the globals, since `test()` has no precondition:
row 68 passes `this` to `B2(B1*)`, and row 69 keeps the pointers in a local `Box`.

brick-lean had recorded candidate A's mechanism on 2026-11-13 as a known hole, and has candidate
B's single revert too ("Prior art"). Stage 0 has not been ported there.

**Status: fixed by stage 0**, SkyLabsAI/BRiCk#564 with SkyLabsAI/auto#756 (merged 2026-11-26; client adaptations
in SkyLabsAI/bluerock.bhv#123 and SkyLabsAI/bluerock.NOVA#46). auto#756 turns rows 68 and 69 into
compiled regressions that `Fail` at `C()` and `~C()`, and adds `tests/virtual/identity_windows`,
which checks the defined calls positively. Stage 0 encodes `Unsettled` as the existing empty-path
token `derivationR cls nil`, which `resolve_virtual` cannot dispatch on, so it adds no predicate
and no axiom. In destructors it unsettles every base right after the members, and settles each base
right before its own destructor. That is stricter than "the bases not yet destroyed stay in phase
`cls`", and loses no defined call: a call through a sibling base during a base destructor is
undefined ([class.cdtor]/4). Stage 1 should keep the same choice for `Gvstruct`, or justify a
different one.

**Residual window: a base initializer's temporaries.** Stage 0 still hands out a settled token in
one window where the call is undefined. `wpi` (`logic/initializers.v`) destroys the temporaries of a
base's mem-initializer (`interp tu free`) *before* its continuation, and that continuation is
`wp_unsettle_identity`. So while those temporaries are destroyed, the base that was just built is
still settled with itself as most-derived class, and a call through it dispatches in that phase. For
`C : B1x, B2` with `B1x : B1`, where a temporary in `B1x`'s mem-initializer calls `b1->f()` on `C`'s
`B1` from its destructor, the rules give `B1x`'s overrider.
- The call is undefined: it runs in `C`'s ctor-initializer before the base mem-initializers have
  completed ([class.base.init]/18). It is also outside the temporary's own object, so the cdtor rule
  does not make it defined.
- Clang and GCC agree with the rules today: at `-O0` and `-O2` both call `B1x`'s overrider (measured
  by the fresh-context review of SkyLabsAI/BRiCk#564). They write `C`'s vptrs either before a base
  initializer (Clang, when it mentions `this`, and then the base's own constructor overwrites them)
  or after all bases (GCC), never between a base's constructor and the end of its mem-initializer.
- That agreement is a property of today's compilers, not of the language. A conforming compiler may
  write `C`'s vptrs right after each base constructor returns, and the gate counts any compiler. The
  rules would then dispatch to `B1x`'s overrider where compiled code reaches `C`'s. This is not a
  gate pass today, but it rests on implementation behaviour the standard leaves free.
- The fix: in base initializers, run `wp_unsettle_identity` right after the constructor returns and
  before the temporaries are destroyed. It loses no defined call. Any call on a subobject of `C` in
  that window is undefined by [class.base.init]/18, and calls on the temporary itself or on
  unrelated objects need no token of `C`.
- Moving `wp_unsettle_identity` before `interp tu free` in `wpi` is not enough. cpp2v wraps an
  initializer that has temporaries in `Eandclean`, and `wp_init_clean` destroys them inside
  `wp_initialize`, so `wpi`'s own `free` is empty. SkyLabsAI/BRiCk#569 (with SkyLabsAI/auto#765)
  makes `wpi_bases` evaluate under a top-level `Eandclean` and destroy the temporaries itself, after
  `wp_unsettle_identity`. Its regression `UC3_ctor_stuck` in auto's
  `tests/virtual/identity_windows` is proved by the stage-0 rules and stuck with the fix.

- **A: early vptr write in `Gstruct` constructors.**
  - The program: `B1` saves `g_b1 = this` and has `virtual int f()` returning 1; `C : B1, B2`
    overrides `f` to return 2; `C() : B2(g_b1->f(), this)`; then `if (c.x == 1) for(;;);`.
  - `wp_init_identity` runs after all base initializers, so `B1`'s token still says `[B1]`, and
    dispatch gives 1.
  - Clang writes `C`'s vptrs before `B2`'s initializer, because it mentions `this`, and returns at
    `-O0` and `-O2`. g++ loops.
- **B: per-base destruction in `Gstruct` destructors.**
  - The program: `C : B1, B2`, `C` overrides `B1::f` (1 → 2), `~B2()` stores `g_b1->f()`, and
    `test()` loops if it stored 1.
  - `wp_revert_identity` puts `B1` back to `[B1]` before `B2` is destroyed, so dispatch gives 1.
  - Both compilers still have `C`'s vtable in `B1`'s slot, and `test()` returns at `-O0` and
    `-O2`.

Both calls are undefined ([class.base.init]/18 for A, and [class.cdtor]/4 for B, since `B1` is not
a base of `B2`). That does not matter for the gate: a proof of `\post False` claims an infinite loop
without UB, so a `test()` that returns refutes it either way. The fixes are the `Unsettled` window and the per-base revert of §2 and §5, applied
to `Gstruct`. They are independent of virtual bases.

**Adequacy tests** (cheapest; positive proofs and `Fail`s, not gate passes):

- During `L`'s construction in `G`, converting `this` to `VB*` yields `G`'s `VB` (from
  `vbase_ptr`, via `vbase_facts_down`), not the offset in a complete `L`. The phase class must not
  determine the layout.
- During the `Unsettled` window, a [class.cdtor]/3 conversion of an already-built base to its
  virtual base succeeds, and a virtual call through it is stuck.
- A hand-built translation unit with two dynamic virtual bases sharing a slot is rejected by
  `vstruct_layout_ok`, and so are `G1` and `G2` from §6.
- An `std::ostringstream` local, constructed, written through `basic_ios` (a `Cderived2vbase`),
  and destroyed, with plain `go`.
- The [class.cdtor]/4 example, with a `V` that holds data (otherwise `V` shares `A`'s slot and §6
  rejects the layout). The defined calls dispatch as the example says, and the undefined
  `a->f()` is stuck.

## Staged plan

0. **`Gstruct` identity windows** (independent of virtual bases): an `Unsettled` state after each
   base constructor, and a per-base revert in destructors (candidates A and B). Implemented in
   SkyLabsAI/BRiCk#564 and SkyLabsAI/auto#756 (merged 2026-11-26), with `Unsettled` as the empty-path token. A
   fresh-context review found it sound (comment on SkyLabsAI/BRiCk#564).
1. **Constructors and destructors with vtables.**
   - Encoding B, with `derivationR` as a definition over `vptrR`. This is needed because `basic_ios`
     is a polymorphic `Gstruct` virtual base.
   - `dyn_state` with `vpath`, `wp_set_identity` in the `Gvstruct` rules, and `tu_no_vtables`
     removed.
   - Dispatch on a target with a virtual step stays `None`.

   This stage is enough for stream objects (construct, convert, destroy). Witnesses 2, 3, 5, 6
   and 9 constrain the bookkeeping, so they belong in this stage's tests as `Fail`s.
2. **Dispatch along non-virtual paths** in hierarchies with virtual bases: `final_overrider` and
   `resolve_virtual` on `dyn_id`, for targets without a virtual step.
3. **Dispatch through a virtual step**, with virtual thunks (witnesses 1 and 4), and covariant
   returns through a virtual base (witness 8).
4. **`delete` through a base pointer** with a virtual destructor: the deleting destructor through
   dispatch, then `resolve_complete_obj`.
5. **Vptr sharing** with nearly-empty virtual bases (§6, witness 7).

## Open questions for Paolo

1. **Order.** *Answered:* stage 0 came first, as its own PRs (SkyLabsAI/BRiCk#564,
   SkyLabsAI/auto#756), before any virtual-base work.
2. **Retire `mdc_path`.** Should it become a definition over `vptrR` (encoding B, with a model for
   `vptrR`)? The alternative is two `Parameter`s (A).
3. **The uninitialized token.** Keep `derivationR cls nil` in `struct_defR`, with a "not
   installed" state, or create tokens in constructors as #549 does and drop them from storage?
   The second option is simpler and matches the abstract `tblockR`, but changes `Gstruct` clients
   that rely on `struct_defR`.
4. **Where `vbase_ptr` comes from at a call through a virtual step:** a premise (no new trust,
   more spec burden), an observation law on `vptrR` (one axiom), or a pointer model in which the
   location follows from the pointer, as brick-lean's `vbaseLoc` (a model change, laws proved)?
5. **Tokens for `Gstruct` classes** that only inherit virtual functions (no `has_vtable`): add
   them now, or keep the current set until dispatch on such classes is needed?
6. **Unsettle before a base initializer's temporaries are destroyed?** *Answered:* yes, as a
   follow-up to stage 0, SkyLabsAI/BRiCk#569 ("Residual window" above).
