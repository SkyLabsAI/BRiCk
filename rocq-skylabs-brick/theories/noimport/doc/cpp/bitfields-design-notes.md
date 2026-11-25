# Bit-fields: design notes and comparison of two designs

*Written by Claude (Fable 5.2) on behalf of Paolo.*

This is a historical record of how the bit-field support (#307) was designed and
why it has its current shape. It is not maintained with the code:

- Sections 1 to 3 are the implementation brief of 2026-11-16. The merged code
  differs in details; read `logic/bitfield.v`, `logic/expr_bitfield.v` and
  `syntax/translation_unit.v` for the current definitions.
- Section 4 is the comparison of the two designs that were implemented, as of
  2026-11-19, and section 5 the nesting-depth measurements behind it.
- Changes after these notes: #505 and SkyLabsAI/auto#711 added `Ebf_andclean`
  (the cleanup of a bit-field full-expression), which removes the "discarded
  bit-field assignment under `Eandclean`" gap of section 4.
- Open work is tracked in #307 and #539, not here.

Two designs for the expression semantics were implemented and compared on one
test suite (`rocq-skylabs-auto-cpp/tests/bitfields` in SkyLabsAI/auto; its
`PLAN.md` states the questions Q1 to Q6 used below). Variant A ("dispatch",
#481, SkyLabsAI/auto#694, SkyLabsAI/skylabs-fm#427) was closed and its branches
deleted; variant B ("separate nodes") was merged as #482, SkyLabsAI/auto#697
and SkyLabsAI/skylabs-fm#428. The pull requests keep the diffs of both.

## 1. Fixed design (both variants)

### Translation-unit metadata
Records with bit-fields are emitted by cpp2v as `Dopaque` (#480). Extend `Opaque'`
(syntax/translation_unit.v) with one field, placed last:

    Record BitfieldInfo : Set := Build_BitfieldInfo
    { bf_run : ident        (* name of the memory location: first named bit-field of the run *)
    ; bf_width : N          (* nonzero *)
    ; bf_signed : signed    (* signedness of the declared type *)
    ; bf_type : type }.     (* declared type, e.g. Tint *)
    o_bitfields : list (ident * BitfieldInfo)

    Definition bitfield_lookup (tu : translation_unit) (cls : globname) (f : ident) : option BitfieldInfo

cpp2v fills `o_bitfields` only for *supported* bit-fields; everything else gets no entry, so accesses
to it are stuck:
- the record is a struct/class, not a union;
- a memory location ("run") is a maximal sequence of adjacent bit-fields of nonzero width
  ([intro.memory]/3): a zero-width bit-field or a non-bit-field member ends it; unnamed
  nonzero-width bit-fields belong to the run but get no entry;
- a run is supported iff every named field in it has a (possibly cv-unqualified) integer type that
  is not bool, char8_t/char16_t/char32_t/wchar_t or an enum, and none is `mutable`; if any field of a
  run is unsupported the whole run gets no entries;
- `bf_run` is the name of the first named field of the run.

### AST leaf
One new `Expr` constructor, next to `Emember`:

    | Ebitfield (arrow : bool) (obj : Expr) (f : ident) (t : type)

emitted by cpp2v for a `MemberExpr` whose member is a `FieldDecl` with `isBitField()`, whatever the
record (also for unsupported ones). `t` is the declared type of the member, as for `Emember`.
`valcat_of`, `type_of`/`decltype_of_expr` etc. treat it exactly like `Emember arrow obj (Nid f) false t`.
There is NO `wp_lval`/`wp_xval`/`wp_operand`/`wp_init` rule for `Ebitfield`. `Emember` is never emitted for a bit-field.

### Rep (new file logic/bitfield.v), axiomatised, no model
    bitfieldsR (cls : globname) (run : ident) (q : Qp) (cs : gmap ident bool) (m : gmap ident Z) : Rep
- `q`: fraction of the memory location; `cs`: per-field const flag, total on the run's named fields;
  `m`: partial, absent = indeterminate.
- Axioms (state as a `Module Type`-free set of `Axiom`s in a clearly marked section, like other
  axiomatised Reps; keep the list minimal and document each):
  timeless; fractional in `q` for fixed `cs`,`m` (`AsFractional`/`FractionalP` style used by auto);
  agreement: `p |-> bitfieldsR cls run q1 cs1 m1 ** p |-> bitfieldsR cls run q2 cs2 m2 |-- [| cs1 = cs2 /\ m1 = m2 |]`;
  validity: `q` ≤ 1 when combined;
  well-formedness, as `Observe`: `dom m ⊆ dom cs`, and for the ambient `σ : genv`:
  every `f ∈ dom cs` has `bitfield_lookup` info with `bf_run = run`, and every `m !! f = Some v`
  satisfies `bitfield.in_range info.(bf_signed) info.(bf_width) v`.
- Pure helpers in the same file or semantics/: `bitfield.trunc (s : signed) (w : N) (v : Z) : Z`
  (reduce modulo 2^w; sign-extend if Signed; reuse `trim`/`to_signed_bits` from arith) and
  `bitfield.in_range s w v : Prop` (decidable; `trunc` lands in range; `trunc` is the identity on in-range values).
- There is deliberately no lemma changing `cs`, and no conversion to or from raw bytes, `anyR`, `tblockR`.

### Judgment for bit-field glvalues (logic/wp.v next to wp_lval)
    Record bf_designator := { bfd_cls : globname; bfd_field : ident; bfd_info : BitfieldInfo }.
    Parameter wp_bitfield_glval : forall {σ : genv}, translation_unit -> region -> Expr -> M (ptr * option bf_designator).
with the same structural axioms `wp_lval` has (shift/fupd, frame, models; NOT well_typed) and the same
derived instances/lemmas automation relies on (`wp_bitfield_glval_wand`, `Proper`, `ElimModal` for fupd...).
`(p, Some d)`: bit-field `d` of the object at `p`. `(p, None)`: the ordinary object at `p`.

Access primitives (definitions, in logic/expr.v or a new logic/expr_bitfield.v), `ty` = erased type of the expression:
- read `(p, None)`: exactly the body of `wp_operand_cast_l2r` (initializedR).
  read `(p, Some d)`: `Exists q cs m v, (p |-> bitfieldsR cls run q cs m ** [| m !! f = Some v |] ** True) //\\ Q (Vint v)`.
- write of `rv` `(p, None)`: exactly the body of `wp_lval_assign` (anyR / tptstoR).
  write `(p, Some d)`: `Exists z cs m, [| rv = Vint z |] ** [| cs !! f = Some false |] ** p |-> bitfieldsR cls run 1 cs m **
  (p |-> bitfieldsR cls run 1 cs (<[f := bitfield.trunc sgn w z]> m) -* Q)`.
- read-modify-write (compound assignment, ++/--): as `wp_lval_bop_assign`/`pre_op`/`post_op`, with the
  `primR ety 1$m v` pair replaced by the bit-field resource before/after and the stored value
  `bitfield.trunc sgn w` of the converted result; the value of post-inc/dec is the old value, the value
  read back from a pre-inc or assignment result is the stored (truncated) value.
- Evaluation order: identical to the existing rules (`eval2 (evaluation_order.order_of ...)`).

Rules common to both variants, stated on `wp_bitfield_glval` for the *leaf*:
    arrow_aggregate_type arrow (decltype_of_expr a) = Some (vc, cv, cls) ->
    bitfield_lookup tu cls f = Some info ->
    (letI* base, free := read_arrow arrow a in Q (base, Some {| cls; f; info |}) free)
    |-- wp_bitfield_glval (Ebitfield arrow a f ty) Q

## 2. Variant A, "dispatch"
- No further AST change. `Fixpoint is_bitfield : Expr -> bool` in syntax (true on `Ebitfield`; through
  `Ecomma _ e`, `Eassign l _ _`, `Eassign_op _ l _ _`, `Epreinc l _`, `Epredec l _`; `Eif _ t e _` if either arm).
- Embedding: `wp_glval e (fun p free => Q (p, None) free) |-- wp_bitfield_glval e Q` (no side condition).
- `wp_bitfield_glval` rules for `Ecomma`, `Eif` (`Reduce (wp_cond wp_bitfield_glval)`), `Eassign`, `Eassign_op`,
  `Epreinc`, `Epredec`, each evaluating its glvalue operand with `wp_bitfield_glval`.
- Sibling consumer rules, each evaluating its operand with `wp_bitfield_glval`:
  `wp_operand (Ecast Cl2r e)`, `wp_operand (Epostinc e ty)`, `wp_operand (Epostdec e ty)`.
- `wp_discard e` becomes: `if is_bitfield e then wp_bitfield_glval e (fun _ => Q) else <existing body>`.
- Existing rules are not changed and get no side conditions.

## 3. Variant B, "separate nodes" (merged)
- cpp2v decides by Clang's `Expr::refersToBitField()` and emits dedicated nodes:
  `Ebf_glvalue (e : Expr)` (embedding of an ordinary glvalue; only as an arm of a bit-field conditional),
  `Ebf_comma e1 e2`, `Ebf_if c t e ty`, `Ebf_assign l r ty`, `Ebf_assign_op op l r ty`, `Ebf_preinc e ty`,
  `Ebf_predec e ty`; consumers `Ebf_postinc e ty`, `Ebf_postdec e ty`, cast `Cl2r_bitfield`.
- `wp_bitfield_glval` has rules only for `Ebitfield` and the `Ebf_*` glvalue nodes; consumers have rules
  only on their `Ebf_*`/`Cl2r_bitfield` node. No `is_bitfield`, no embedding rule, no sibling rules on
  standard nodes. `wp_discard` matches the head constructor (non-recursive).
- No rule may depend on nesting depth; nodes nest arbitrarily.

## 4. Comparison: dispatch (A) vs separate nodes (B)

Outcome (2026-11-19): the separate-node variant (B) was chosen. A's extra
failed hint applications are negligible (Q2), so performance does not separate
the variants; B was preferred because a dedicated constructor gives the
automation the most efficient discrimination: every rule and hint is selected
by the head constructor alone. The opaque-record, dispatch and separate-node
PR sets were then combined into #482, SkyLabsAI/auto#697 and
SkyLabsAI/skylabs-fm#428; the other six PRs were closed. The suite was trimmed
afterwards (nesting at depth 3 only, one translation unit): its new files cost
555 Ginstr (+0.29%), down from 869. Combining test functions was tried and
undone: it saved only 21 Ginstr. The per-variant numbers below predate the
trimming.

| | Dispatch (A) | Separate nodes (B) |
|---|---|---|
| PRs | #481, SkyLabsAI/auto#694, SkyLabsAI/skylabs-fm#427 (closed) | #482, SkyLabsAI/auto#697, SkyLabsAI/skylabs-fm#428 (the combined set, merged) |
| New Expr/Cast constructors | 1 (`Ebitfield`) | 10 (`Ebitfield`, 9 `Ebf_*`) + `Cl2r_bitfield` |
| BRiCk rule axioms | 11 | 11 |
| Recursive `is_bitfield` | yes | no (head test `is_bf_glvalue`) |
| Embedding of `wp_glval` | on every expression | only on `Ebf_glvalue e` |
| cpp2v change | leaf only | leaf + per-node `refersToBitField()` (~60 lines) |

### Q1 Soundness
No soundness bug found in either. All 18 negatives (plus `compound_u`,
`bind_tmp`) stay stuck in both, for the same reasons. A's unconditional
embedding is sound only because `wp_lval` has no rule for `Ebitfield`; B does
not rely on that.

### Q2 Cost for existing code
- A: three consumer hints (l2r cast at 147, post-inc/dec at 199) sit just
  ahead of the existing hints, each guarded by `is_bitfield e =[Vm]=> true`.
  Every existing l2r / post-inc / post-dec pays one vm guard. Discarding a
  non-bit-field glvalue additionally reduces `is_bitfield` in the `cbn` pass
  (one step per node on the followed path, both arms of a conditional).
- B: no bit-field hint on a pre-existing node, no guard. A probe with the
  bit-field hints removed leaves goals on the new nodes untouched.
- Wall-clock on the plain nest twins shows no difference beyond noise in
  either.
- CI performance, in Ginstr (10^9 instructions), with the nesting benchmark
  at depths 1, 4 and 16. Both runs report 0 errors and no new warnings, and
  include the bhv/NOVA proofs.

  | | A vs the Gopaque base (run 44381263358) | B vs A (run 44381275446) |
  |---|---:|---:|
  | Total | +964.6 (+0.50%) | -34.1 (-0.02%) |
  | New files (24) | +863.2 (+0.44%) | none |
  | Existing files | +101.4 (+0.05%) | |
  | Translation units | | +8.0 (+0.02%) |
  | Proofs and tests | | -42.1 (-0.03%) |

  B is stacked on A, so its run measures the difference directly. Everything
  on existing files is inside the +-0.2% noise band: CI performance does not
  separate the variants.
- CI hint data (`hint-data.csv` of the same runs, `hintOK`/`hintKO` spans
  aggregated by full hint name; B's reference build is byte-identical to A's
  job build):

  | | Successes | Failures |
  |---|---:|---:|
  | Gopaque base | 487,441 | 1,616,761 |
  | A | 495,494 | 1,631,882 |
  | B | 495,494 | 1,629,072 |

  A has 2,810 more failed applications than B, all in its guarded consumer
  hints:

  | Hint | A (OK / KO) | B (OK / KO) | Extra failures in A |
  |---|---:|---:|---:|
  | `wp_operand_cast_l2r_bitfield_B` | 43 / 2311 | 43 / 84 | 2227 |
  | `wp_operand_postinc_bitfield_int_B` | 4 / 321 | 4 / 84 | 237 |
  | `wp_operand_postinc_bitfield_uint_B` | 0 / 325 | 0 / 88 | 237 |
  | `wp_operand_postdec_bitfield_int_B` | 2 / 136 | 2 / 84 | 52 |
  | `wp_operand_postdec_bitfield_uint_B` | 0 / 138 | 0 / 86 | 52 |

  The remaining 5 are A's `wp_bitfield_glval_plain_B` (20 / 89) against its
  B counterpart `wp_bitfield_glval_glvalue_B` (20 / 84).
  - The failures are on existing code: the l2r hint is tried, and its guard
    fails, on every ordinary lvalue-to-rvalue read that a hint handles. 2,232
    of its failures end in the `subgoals` phase, exactly the number of
    successes of the four regular `wp_operand_cast_l2r_*` hints in that run
    (2,225 in the base run, so 7 come from the new tests).
  - Cost: about 14.5 Ginstr (12.1 for l2r, about 5.3 Minstr per attempt),
    0.007% of the 194,090 Ginstr workspace.
  - Assignment, pre-increment, comma and conditional hints have identical
    counts in A and B.
  - Base to A, failures rise by 15,121; B shares all but the 2,810 above, so
    the rest comes from the new test files and the shared `bitfieldsR` hints.
  - Not attributed per file: the CI artifact aggregates over the workspace,
    and the local build embeds no profiling data.

### Q3 Depth scaling (64/32 time ratio, bf families)
A: 1.65-1.93. B: 1.68-2.08. Both linear; all 98 nest theorems pass in both.
Measured once at depths 1..64 (`nest_gen.py --all-depths`); CI now checks
depths 1, 4 and 16 (42 theorems).

### Q4 Compositionality
- A: rules live on standard nodes, so each standard node has two rules and
  the choice is made by `is_bitfield` (in `wp_discard`, in hint guards).
- B: every rule mentions only its own node.
- But B has a cost A does not: `Wp.wp_expr_discard` needs the premise
  `valcat_of e = Prvalue \/ is_bf_glvalue e = false`, and the template hint
  `wp_discard_Eresolved_unop_B` a guard that cannot be discharged for an
  abstract resolved unop, so that hint no longer fires on glvalue results
  (e.g. a discarded template `++x`). No test covers it. A (after reordering
  `wp_discard`) needs no change to existing lemmas or hints. B could get the
  same with an axiom `is_bf_glvalue e = true -> wp_lval e Q |-- False`
  (and for `wp_xval`); not added: design decision.

### Q5 Change cost
- BRiCk: B is +495/-101 over A in 14 files (8 syntax files).
- auto: B differs from A in 8 files, +148/-80; `pattern.v` needs 9 more
  matchers. Template instantiation of `Ebf_*` nodes into resolved operators is
  not handled in B.
- skylabs-fm: identical one-commit update of scope reports.

### Q6 Client equivalence
Specs and proof scripts of all tests/bitfields proofs are byte-identical
between the variants. bhv/NOVA proofs build unchanged in CI with both.

### Gaps shared by both variants, as of 2026-11-19
- Promotion-sensitive read-modify-write stuck (`s.u -= 1`, also blocked by
  `tr = type_of r` in the compound-assignment rule).
- `const int&` bound to a bit-field: cpp2v emits `Eunsupported`.
- Discarded bit-field assignment under `Eandclean`, GNU `?:`, `Cnoop`.
- `bitfieldsR` gives no `type_ptrR`, so `->`/`this`/nested access needs it in
  the spec.
- `promote` needs a manual `to_signed_id` rewrite.
- Hints cover `int`/`unsigned int` and C++17 evaluation order only.
- No model of `bitfieldsR`; no construction/destruction/copy.

## 5. Nesting-depth measurements

Seconds of automation per theorem (`verify_spec` and `go`, `Qed` excluded) for
each family of the generated nesting benchmark (`nest_gen.py --all-depths` in
the suite), at depths 1 to 64, with the ratio of depth 64 to depth 32. The
`plain` twins have an ordinary `int` in place of the bit-field. Measured once
per variant on 2026-11-16 on a loaded machine, so differences of a few tenths
of a second are noise; a ratio near 2 means linear cost. `inc_plain` is
super-linear in all three tables, including the baseline without any bit-field
support, so that is a property of existing automation.

Baseline (before the bit-field support; plain twins only):

```
family                 1       2       4       8      16      32      64   64/32
comma_rd_plain      1.08    0.97    1.80    1.68    2.33    3.48    6.53   1.88
comma_wr_plain      0.82    0.95    1.35    1.56    2.28    3.46    6.49   1.88
cond_rd_plain       1.24    1.39    2.08    1.94    2.55    3.93    6.91   1.76
inc_plain           0.73    0.84    1.28    1.47    2.36    5.38   19.15   3.56
assign_plain        0.77    0.89    1.19    1.21    1.45    2.77    4.39   1.58
alt_plain           0.77    1.21    1.30    1.38    1.81    2.98    5.62   1.88
cond_wr_plain       1.16    2.52    1.78    1.91    2.45    3.82    6.70   1.75
```

Variant A:

```
family                 1       2       4       8      16      32      64   64/32
comma_rd_bf         1.00    1.08    1.25    1.60    2.08    3.62    6.55   1.81
comma_rd_plain      1.04    1.03    1.07    1.52    2.31    3.79    6.61   1.75
comma_wr_bf         0.91    0.95    1.10    1.50    2.15    3.50    6.18   1.76
comma_wr_plain      1.00    0.98    1.03    1.47    2.14    3.43    8.49   2.48
cond_rd_bf          1.33    1.45    1.55    1.82    2.58    3.87    6.49   1.68
cond_rd_plain       1.42    1.43    1.60    1.92    2.54    3.86    7.47   1.94
inc_bf              0.76    0.81    1.05    1.45    2.16    3.97    7.68   1.93
inc_plain           0.81    0.86    1.31    1.35    2.50    5.31   19.49   3.67
assign_bf           0.81    0.83    1.02    1.35    1.83    3.43    5.69   1.66
assign_plain        0.77    0.85    1.21    1.09    1.47    2.21    4.95   2.24
alt_bf              0.79    0.88    1.08    1.67    2.58    4.26    8.16   1.92
alt_plain           0.81    1.01    1.39    1.28    1.85    3.00    6.23   2.08
cond_wr_bf          1.24    1.51    1.34    1.84    2.59    4.09    6.76   1.65
cond_wr_plain       1.30    1.40    1.63    1.84    2.62    3.93    7.57   1.93
```

Variant B:

```
family                 1       2       4       8      16      32      64   64/32
comma_rd_bf         1.43    1.19    1.31    2.18    2.29    3.93    6.61   1.68
comma_rd_plain      1.48    1.42    1.53    1.51    2.41    3.88    6.93   1.78
comma_wr_bf         1.64    1.03    1.19    1.52    2.12    3.65    7.08   1.94
comma_wr_plain      1.91    1.35    1.16    1.44    2.63    3.68    6.75   1.83
cond_rd_bf          1.55    1.72    1.79    1.89    2.51    4.02    6.86   1.71
cond_rd_plain       1.72    2.05    1.64    1.84    2.79    4.18    7.30   1.75
inc_bf              0.90    1.07    1.10    1.36    2.32    4.18    8.70   2.08
inc_plain           1.08    1.14    1.02    1.35    2.45    5.71   19.75   3.46
assign_bf           0.96    1.08    1.06    1.55    2.01    3.23    6.42   1.99
assign_plain        0.99    1.18    1.31    1.05    1.60    2.32    5.47   2.36
alt_bf              1.30    1.34    1.46    2.10    3.27    4.67    9.02   1.93
alt_plain           1.05    1.15    1.59    1.33    1.83    3.20    6.84   2.14
cond_wr_bf          1.83    2.07    2.00    1.95    2.61    4.19    8.24   1.97
cond_wr_plain       1.49    1.56    2.13    1.92    2.54    3.90    7.16   1.84
```
