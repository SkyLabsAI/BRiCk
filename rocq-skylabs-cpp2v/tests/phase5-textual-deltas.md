# Phase 5 owned-emitter parity and textual delta audit

This audit records the gate run immediately before removing the temporary
legacy/owned switch. `phase5-parity-manifest.tsv` classifies all 195 retained
C++ or header test inputs (175 production inputs), and `phase5_manifest.t`
prevents the set from silently shrinking. The removed 196th input was the
now-obsolete test-only legacy semantic parity probe. Phase 6 subsequently added
one production companion fixture, so the live manifest now reports 196 inputs
(176 production) without changing this historical Phase 5 gate count.
The frozen Phase 0 legacy baselines remain unchanged as historical oracles.

## Semantic gate

All comparisons below compile both generated Rocq modules and prove complete
definition equality with `vm_compute; reflexivity`. There are no one-sided-map
or exhaustive-field exceptions.

- The actual complete Cram corpus passed with the temporary owned-selection,
  semantic-parity, and parity/no-sharing gate switches enabled. Every
  `check_cpp2v*` fixture therefore
  proved whole `source` equality in both sharing modes; template fixtures also
  proved whole standalone `templates` equality in both modes.
- All 45 Makefile-managed production inputs passed whole ordinary and template
  equality in both sharing modes (90 comparisons), including `preprint.t`,
  `std_pair.t` under GNU C++23, self-typedef cases, bitfields, and every valcat
  input.
- The seven manually classified production inputs passed explicit parity.
  Additional runs covered both target triples and a C++20 `test_decompose`, for
  18 successful sharing/no-sharing comparisons.
- A mode matrix passed combined, combined/no-sharing, static-only,
  static-only/no-sharing, combined interactive, static interactive,
  templates-only, simultaneous `-o` plus `--templates`, stdout, and
  `--no-aliases` ordinary/template equality.
- C++17 and C++20 declaration-builder oracles pass independently; the complete
  corpus includes its declared C++17/C++20 cases and the C++23 standard-library
  case.
- Name tests remain a separately classified diagnostic path. Reject and partial
  output fixtures passed their ordinary Cram expectations rather than semantic
  equality, and focused builder/source-extraction fixtures passed their own
  Cram proofs.

Gate logs were written outside the repository as:

- `/tmp/phase5-full-cram-both-sharing-final-3.log`
- `/tmp/phase5-makefile-scan-both.log`
- `/tmp/phase5-manual-parity.log`
- `/tmp/phase5-mode-matrix-final.log`

## Characterized text changes

The generated files are intentionally not byte-identical. Every change falls
into one of the following classes; none changes the folded translation unit.

1. **Direct final insertions.** Ordinary parser constructors such as
   `Dfunction`, `Dstruct`, and `Dtypedef` are replaced by `Dobj_value` or
   `Dglob_decl` applied to the already-final `ObjValue`/`GlobDecl`. Template
   declarations similarly use `Dtemplated_obj_value` or
   `Dtemplated_glob_decl`; aliases and instances use
   `Dtemplated_type_alias` and `Dtemplate_preinst`. This is the intended
   removal of parser-side semantic reconstruction.
2. **Eager helper reduction.** Parser/mparser-only syntax is absent after its
   final core result is built in C++. For example, template `Esizeof_pack None`
   becomes final `Eunresolved_sizeof_pack`, while a selected static pack size
   is an `Eint`; erased helper arguments no longer appear in the term or its
   location children. Similar differences cover final static methods, enum
   constants, adjusted/deduced types, and direct template pre-instantiations.
3. **Owned sharing definitions.** Definition numbering, count, and order can
   change because sharing is now analyzed over validated semantic nodes.
   Dependencies precede names, ordinary variable names are not seeds, only
   semantically equal representatives reuse a class, one ordinary-seeded plan
   serves both combined partitions, and templates-only output stays inline.
   As a representative size characterization, `test_decompose` combined output
   changed from 8,643 to 3,229 lines and no-sharing output from 8,100 to 2,615
   lines. Sharing and no-sharing nevertheless prove the same complete values.
4. **Formatting and canonical spelling.** Owned events are emitted one per
   line rather than through the legacy formatter's nested indentation.
   Parentheses and explicit core qualifications may differ, final scalar types
   use their canonical constructors, and negative Rocq integers are rendered
   as parenthesized `%Z` terms. These are parser-equivalent spelling changes.
5. **Diagnostic comments.** `--comment` remains supported. The owned unit stores
   Clang-derived diagnostic spellings while Clang is live, and the Clang-free
   emitter escapes and places them adjacent to direct insertion arguments.
   Representative ordinary and template outputs have the same comment counts
   and comment text as the legacy output; only surrounding constructor syntax
   and line layout differ.
6. **Framing remains stable.** Imports, scopes, ABI conversion, attributes,
   static/meta composition, deprecated `module` abbreviation, `--check-types`,
   interactive sections, and atomic `.partial` publication remain outside the
   semantic emitter. Their text is unchanged except where changed semantic
   lines alter indentation boundaries.
7. **Diagnostics and failure timing.** A migration rejection is now reported as
   owned IR construction failure before semantic emission. Supported fixtures
   have no such rejection. Existing reject and partial-file Crams establish
   recoverable diagnostics and atomic-output behavior. Legacy semantic-visitor
   trace messages disappear with that visitor; ModuleBuilder/elaboration traces
   and the distinct name-diagnostic trace path remain available.

## Post-switch architecture

After this gate, the temporary CLI/environment selection and parity hooks and
the test-only legacy semantic probe were removed. Semantic outputs now build
one owned unit unconditionally and have no fallback branch. A name-test-only
request deliberately skips complete semantic construction and retains its
isolated diagnostic name formatter. `architecture.t` and the mandatory
`cpp2v-architecture-tests` alias check that builders cannot reach output APIs,
node constructor spellings remain registered, direct insertion helpers remain
in `RocqEmitter.cpp`, the semantic orchestration has no legacy calls, and the
pure IR/emitter layer is Clang-free. The complete ordinary post-switch Cram corpus passed; the final log is
`/tmp/phase5-post-switch-full-cram-final.log`. Repeated production generation
of the frozen fixture was byte deterministic and produced owned-output hashes
`edd254bde2291121d3a832647b6b91384a4556a402d0fd64460f4c5c8e045e7c`
(default sharing) and
`75b3ce6e18e719eeb4ead5dcd881a31cb8040b1d2796578cf438fd7b36382fcc`
(no sharing). The checked-in Phase 0 legacy oracle files retain their original
hashes rather than being rewritten.

Repeated generation remains byte deterministic within each audited configuration.
The large one-hunk diffs are explained by direct final insertion plus formatting
and sharing changes; complete Rocq equality, symmetric cardinalities, and the
fixture manifest establish that they do not hide semantic deltas.
