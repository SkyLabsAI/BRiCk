# Terminal cleanup suffix duplication: design and examples

Draft by Codex, 2026-11-23, for [SkyLabsAI/BRiCk#515](https://github.com/SkyLabsAI/BRiCk/issues/515).
This directory collects design evidence. It does not implement goto support,
change trusted rules, or establish a Rocq soundness proof.

## Required scope

Local declarations and explicit cleanup before returns are requirements for
the first useful implementation. Supporting only `goto L` where `L: return e`
occurs in a declaration-free function would solve the issue's small reproducer
but miss the resource-management idiom we want.

The proposed first implementation accepts common-scope cleanup ladders with
local variables. It lowers each accepted jump to the **complete terminal
suffix** at its destination. For the requested example:

| Destination | Copied suffix |
| --- | --- |
| `actions_fail` | `freeResource(res2); freeResource(res1); return errorcode;` |
| `res2_fail` | `freeResource(res1); return errorcode;` |
| `res1_fail` | `return errorcode;` |

Labels within a suffix are erased, not treated as extra executions. A Clang
`LabelStmt` wraps only its immediate substatement: using just `getSubStmt()`
would omit the following cleanup and return. Extraction must retain subsequent
siblings through the terminal return.

## The supplied example is C, not well-formed C++

[examples/original.c](examples/original.c) preserves the supplied Stack Overflow
example, with a fixture header and an explicit `void` parameter. Its first jump
to `res1_fail` bypasses the initialized declaration of `res2` in the same block.
C++ prohibits that jump even though the destination does not read `res2`.
See [the C++ draft, stmt.dcl/2](https://eel.is/c++draft/stmt.dcl#2).

For scalar or pointer handles, a valid common-scope spelling is:

```cpp
int errorcode = 0;
handle_t res1 = getResource();
handle_t res2 = 0;              // exists before every jump
if (!res1) { errorcode = somethnig; goto res1_fail; }
res2 = getResource();           // acquisition still happens only after success
// Remaining code and cleanup labels as before.
```

This is an explicitly different source example, not a proposed automatic repair
of ill-formed C++. Moving arbitrary class-valued initializations can change
observable behavior and is not part of this design. The fixture chooses integer
handles and checks that acquisition/release/action traces are unchanged.
The original `if (!errorcode)` tests are retained literally.

Parsing C input and validating its different lifetime/initialization rules would
be a separate scope decision. This proposal targets well-formed C++ input.

## Proposed accepted subset

1. Ordinary scalar/void-returning functions and direct forward jumps. Initially
   exclude constructors/destructors, coroutines, NRVO returns, computed jumps,
   assembly, exception regions, and jumps involving loop/switch control contexts.
2. Targets are top-level labels in the function body. Their complete terminal
   suffixes contain only already-supported expression statements and an explicit
   scalar/void return, with optional intervening labels. No declarations or
   gotos occur in copied suffixes. More complex terminating conditionals can be
   a later extension with a separate termination/continuation check.
3. Local declarations before the jumps are allowed. Each jump has the same
   ordered live bindings, active object lifetimes, and pending cleanup at its
   source and destination. Empty nested blocks and conditionals are fine when
   they introduce no additional live objects. If-init and condition declarations
   must be included in this check.
4. Free local references in the copied AST retain their binding identities in
   the source region. A matching type or matching name spelling is insufficient.
5. All relevant statements/expressions are classified before emitting output.
   Unsupported wrappers, GNU statement expressions, lambda bodies, and hidden
   control transfers must not escape validation. Function/lambda label namespaces
   remain separate; use declaration identity rather than label text as a key.

Nontrivial locals already live at both points are compatible with this design:
the explicit cleanup executes, the return expression is evaluated, and then
the original automatic cleanup runs. Do not manually destroy these locals
before the copied suffix. Existing `Kfree` continuations already handle their
ordinary function exit. See [examples/same_scope.cpp](examples/same_scope.cpp).

Same live context is a sufficient conservative criterion, not a claim that it
is necessary for every correct transformation. For example, declarations in
unrelated blocks completed before the target need not prevent acceptance.

## Normalization and soundness argument

Perform a whole-function analysis in cpp2v, then emit either the validated
normalized body or the original unsupported body. Keep declarations and all
unrelated source statements in place. Replace each accepted goto with a block
containing its target's full suffix; unwrap the validated original labels.
Retain original return nodes and their resolved expressions/source context.
Do not add lambdas or helper functions as a shortcut for suffix sharing.

For every accepted edge:

- The original jump performs no lifetime transition and has no expression
  evaluation. The destination and copied suffix therefore start with the same
  live objects, store, bindings, and cleanup obligations.
- Both execute the same supported effects in the same order. The inserted
  block has no declarations and changes no local bindings.
- Both evaluate the same return expression before the same automatic cleanup.
- The return bypasses the source continuation, preventing later source
  statements or the original cleanup suffix from executing a second time.
- Ordinary fallthrough still executes the original cleanup suffix once.

This explains the intended transformation; it is not a checked theorem. cpp2v
is a trusted translation boundary. The existing abstract `wp` interface has no
goto semantics from which this equivalence can currently be derived. Adding no
Rocq axiom does not eliminate the frontend correctness obligation.

## Why scope-crossing remains excluded

Local variables themselves are not the problem. Changing which objects are live
while running the copied cleanup is the problem.

[examples/counterexamples.cpp](examples/counterexamples.cpp) contains executed,
defined-behavior comparisons that refute unsafe variants:

| Incorrect rewrite | Original | Naive result |
| --- | ---: | ---: |
| Evaluate destination return before scope-exit destructor | 7 | 1 |
| Bind destination expression to source's shadowing local | 1 | 2 |
| Copy only destination statement, then resume source suffix | 1 | 3 |

Checking only destructor triviality or the suffix's explicit free variables is
insufficient. In `examples/rejected.cpp`, an escaped pointer refers to a local
whose lifetime ends at the goto; moving the suffix before that lifetime end makes
an invalid read appear valid. That example is **compile-only**, never executed,
and is not a defined-behavior result comparison or a gate pass. A callee can hide
the same alias, so explicit syntactic references alone cannot justify moving it.

A nested-block cleanup ladder may be well-formed C++ but still cross these
lifetime boundaries. Supporting it requires restructuring branches to execute
the suffix after the original scope exits, a sufficient lifetime/escape argument,
or explicit transfer/cleanup semantics. That is outside direct substitution.

## Size and invasiveness

The chosen algorithm is **terminal cleanup suffix duplication**. This name
refers only to copying original, goto-free terminal cleanup suffixes once at
each accepted goto. It does not recursively expand gotos in copied code.

Let N be the original body size in AST nodes, G the number of replaced gotos,
and C_i the size of the original terminal cleanup suffix copied at goto i.
The generated AST size is

    O(N + sum_i C_i) <= O(N + G*C_max) <= O(N^2).

The bound is on total output size. Relative to an N-node input, the worst-case
multiplicative growth factor is O(N), not O(N^2). The quadratic total-size bound
is attainable: G conditional gotos can all target one C-node cleanup suffix,
with G and C both proportional to N. If cleanup suffix length is bounded by a
constant, total generated size is instead O(N).

For the collected resource ladder, the four gotos copy respectively 1, 2, 3,
and 3 statements, counting cleanup calls and returns. That adds 9 statement
occurrences to the original 3-statement cleanup suffix, for 12 cleanup/return
statement occurrences. This deliberately excludes expressions, block wrappers,
and unrelated statements; it is an illustrative count, not an exact AST count.
Each execution still takes only one of those copies or the original suffix.

| Cost | What the design establishes |
| --- | --- |
| Generated cpp2v AST size | O(N + sum_i C_i), at most O(N^2); no exponential recursive duplication |
| Emitting the generated AST | Linear in its output size with a straightforward implementation |
| Validation | A straightforward repeated walk/context comparison can fit O(N^2) under unit-cost AST/binding operations; no implementation or timings exist yet |
| Rocq elaboration/checking and `go` time | More syntax and repeated cleanup obligations; the AST bound is not an upper bound on tactic search or kernel checking time |
| Executable C++ runtime/binary size | Unchanged by this proposal: cpp2v normalizes the verification AST, while the original C++ source remains the compiler input |

The hand-written native comparison programs are validation artifacts, not a
proposal to replace production C++ source. Even if compiled independently,
terminal cleanup suffix duplication executes the same cleanup calls in the same
order on each path; it does not execute every generated copy. Any machine-code
size/cache effects in that different deployment would require measurement.

[growth.py](growth.py) demonstrates why unrestricted recursive goto expansion
has no such bound: an O(n)-stage forward-jump program expands by the recurrence
T(n) = 2*T(n-1) + O(1). Eight stages produce 256 returns; twelve produce 4,096.
The eight-stage expanded program is checked against all 256 branch choices.
The family has an easy linear structured rewrite; it disproves a bound on naive
expansion, not the existence of a better algorithm.

This useful subset is a moderate frontend change: a whole-function collector,
suffix extraction, live-context/binding checks, controlled printer output,
diagnostics/documentation, and translation/client proof tests. It needs no
change to `ReturnType` or ordinary `go` interfaces. General goto handling or
scope-crossing restructuring is materially larger.

## Evidence inventory and running it

| File | Role |
| --- | --- |
| `examples/original.c` | Supplied ladder: positive C compile, negative C++ compile |
| `examples/resource_ladder.cpp` | Valid C++ ladder and manually lowered output; check all 16 fixture choices against the C original and independent expected traces |
| `examples/same_scope.cpp` | Positive same-scope RAII cleanup and issue's clamp example |
| `examples/counterexamples.cpp` | Executed negative examples for incorrect transformations |
| `examples/rejected.cpp` | Valid C++ inputs requiring rejection by the future validator; compile-only |
| `growth.py` | Reproducible exponential-expansion example |
| `check.py` | Standalone native checks; binaries/generated files go in a temporary directory |

Run from the workspace root through the prescribed Linux build container:

```sh
python3 fmdeps/BRiCk/rocq-skylabs-brick/doc/design/goto-cleanup/check.py
```

`CC` and `CXX` override the compiler commands; defaults are `clang` and
`clang++`. Checks run defined-behavior comparisons at both `-O0` and `-O2`.
They do not build Rocq or require workspace Dune installation. This directory
is a standalone design corpus, not yet integrated into Cram or cpp2v tests.

The initial run on 2026-11-23 passed in the prescribed workspace container,
using Clang 22.1.8 on x86_64 Linux. [validation.log](validation.log) records the
compiler diagnostic, both optimization-level runs, and growth results.
Diagnostic paths in the log are normalized to repository-relative paths. The
resource fixture checks 16 choices against independent expected return values
and event traces for all three versions. The RAII fixture checks return values
and the subsequent destructor effect. These finite checks support the examples;
they do not prove the transformation for arbitrary programs.

No normalizer exists yet: positive/negative labels describe its intended
contract. The runner does not claim to exercise validator acceptance/rejection.
When implementing it, promote cases into actual frontend and `go` regressions,
including support-report checks and a proof of the valid resource ladder under
resource acquisition/release specifications. Do not retain development-only
`Print Assumptions` output when turning a fixed witness into a regression.

## Adversarial review and gate-search boundary

The initial proposal was reviewed independently for semantic correctness,
native counterexamples/size, and current gate exposure. A subsequent review
specifically challenged local declarations and the resource ladder, finding the
escaped-trivial-local boundary and the need to copy all label siblings.

Static inspection at BRiCk `45c638f3e835981d6695277efee674002e0c302a` and auto
`526f893d15d1ea5265bb1406f3607c0ac5261b89` found no goto-specific gate pass:

- `syntax/supported.v` rejects `Slabeled` and `Sgoto`.
- No corresponding statement WP rule exists; the soundness inventory already
  records them as unsupported, not known wrong.
- `syntax/stmt.v` checks `no_case` through labels; switch simplification does
  not erase goto/labels, and `may_exit` treats goto conservatively.

No Rocq gate witness was compiled. Native semantic mismatches above refute
proposed bad transformations, not current BRiCk. A future gate search must use
the exact cpp2v-generated program and baseline assumptions; unrelated known
inconsistencies or an assumed proposed rule would not establish a goto defect.

## Attribution

The resource ladder is from [KamilCuk's Stack Overflow answer](https://stackoverflow.com/a/70446256),
as supplied by the user, retrieved 2026-11-23. `examples/original.c` and
`examples/resource_ladder.cpp` preserve its CC BY-SA 4.0 attribution and license
notice. The latter adds the C++ spelling, hand-lowering, and trace harness.
