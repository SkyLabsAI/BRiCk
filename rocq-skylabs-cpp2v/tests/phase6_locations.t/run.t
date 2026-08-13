  $ . ../setup-project.sh
  $ . ../setup-cpp2v.sh

One cpp2v invocation produces an ordinary AST module and a standalone location
companion. Both compile, and a query reaches the initializer expression through
a nonempty shape path and recovers its physical source line.

  $ check_cpp2v_locations fixture.cpp
  cpp2v -v -check-types -o fixture_17_cpp.v --locations fixture_17_cpp_locations.v fixture.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix fixture_17_cpp.v
  rocq c -w -notation-overridden -w -notation-incompatible-prefix fixture_17_cpp_locations.v
  $ rocq c $ROCQC_ARGS check.v
  $ grep -q 'compact root events: .* selected; .* singleton; .* residual' fixture_17_cpp_locations.v
  $ grep -q '(CIL(' fixture_17_cpp_locations.v
  $ ! grep -q '(Ovar ' fixture_17_cpp_locations.v
  $ grep -q 'residual_root_events : list Construction.filtered_indexed_located_root_event' fixture_17_cpp_locations.v
  $ test ! -e fixture_17_cpp.v.partial
  $ test ! -e fixture_17_cpp_locations.v.partial

Inline mode publishes one file containing the exact location stream followed by
the exact AST stream. Locations come first because the parser imported by the
AST installs a global `[` grammar that conflicts with primitive-array literals.
Both generated values compile and the same lookup proof works after importing
only that file. No inferred companion is created, and the single stream may be
written to stdout.

  $ cat fixture_17_cpp_locations.v fixture_17_cpp.v > inline_expected.v
  $ rm -f inline_locations.v
  $ cpp2v -o inline.v --locations-inline --check-types fixture.cpp -- -std=c++17
  $ cmp inline_expected.v inline.v
  $ rocq c $ROCQC_ARGS inline.v
  $ sed 's/Require Import fixture_17_cpp_locations\./Require Import inline./' check.v > inline_check.v
  $ rocq c $ROCQC_ARGS inline_check.v
  $ test ! -e inline_locations.v
  $ test ! -e inline.v.partial
  $ cpp2v --module - --locations-inline --check-types fixture.cpp -- -std=c++17 > inline_stdout.v
  $ cmp inline.v inline_stdout.v

The explicit all-files scope changes only the companion and uses the unchanged
legacy construction spelling.

  $ cpp2v -o all_files.v --locations all_files_locations.v --locations-all-files --check-types fixture.cpp -- -std=c++17
  $ cmp fixture_17_cpp.v all_files.v
  $ rocq c $ROCQC_ARGS all_files_locations.v
  $ grep -q 'residual_root_events : list Construction.indexed_located_root_event' all_files_locations.v
  $ grep -q 'Construction.build_lazy_compact_indexed_dag_source_map_or_fail' all_files_locations.v
  $ ! grep -q 'filtered_indexed_located_root_event' all_files_locations.v
  $ cat all_files_locations.v all_files.v > all_files_inline_expected.v
  $ cpp2v -o all_files_inline.v --locations-inline --locations-all-files --check-types fixture.cpp -- -std=c++17
  $ cmp all_files_inline_expected.v all_files_inline.v
  $ rocq c $ROCQC_ARGS all_files_inline.v

The table-specific construction fold selects exactly the parser's value and the
corresponding tree for equal duplicates, compatible unequal declarations,
self-typedef suppression, and template overwrites.

  $ rocq c $ROCQC_ARGS fold_check.v

Location serialization is deterministic and independent of ordinary sharing.
The same input is emitted again, then with ordinary sharing disabled.

  $ cpp2v -o repeat.v --locations repeat_locations.v --check-types fixture.cpp -- -std=c++17
  $ cmp fixture_17_cpp.v repeat.v
  $ cmp fixture_17_cpp_locations.v repeat_locations.v
  $ cpp2v -o unshared.v --locations unshared_locations.v --no-sharing fixture.cpp -- -std=c++17
  $ rocq c $ROCQC_ARGS unshared.v
  $ rocq c $ROCQC_ARGS unshared_locations.v
  $ cmp fixture_17_cpp_locations.v unshared_locations.v
  $ cat unshared_locations.v unshared.v > unshared_inline_expected.v
  $ cpp2v -o unshared_inline.v --locations-inline --no-sharing fixture.cpp -- -std=c++17
  $ cmp unshared_inline_expected.v unshared_inline.v
  $ rocq c $ROCQC_ARGS unshared_inline.v

Suppressing templates also suppresses both template location maps while the two
outputs remain valid.

  $ cpp2v -o no_templates.v --locations no_templates_locations.v --no-templates fixture.cpp -- -std=c++17
  $ rocq c $ROCQC_ARGS no_templates.v
  $ rocq c $ROCQC_ARGS no_templates_locations.v
  $ rocq c $ROCQC_ARGS no_templates_check.v
  $ grep -q 'singleton_msymbol_events : list (name \* indexed_location) := nil' no_templates_locations.v
  $ grep -q 'singleton_mtype_events : list (name \* indexed_location) := nil' no_templates_locations.v
  $ ! grep -Eq '\((CRMS|CRMT)\(' no_templates_locations.v
  $ cpp2v -o no_templates_all_files.v --locations no_templates_all_files_locations.v --locations-all-files --no-templates fixture.cpp -- -std=c++17
  $ rocq c $ROCQC_ARGS no_templates_all_files.v
  $ rocq c $ROCQC_ARGS no_templates_all_files_locations.v
  $ grep -q 'singleton_msymbol_events : list (name \* indexed_location) := nil' no_templates_all_files_locations.v
  $ grep -q 'singleton_mtype_events : list (name \* indexed_location) := nil' no_templates_all_files_locations.v
  $ ! grep -Eq '\((CRMS|CRMT)\(' no_templates_all_files_locations.v
  $ cat no_templates_locations.v no_templates.v > no_templates_inline_expected.v
  $ cpp2v -o no_templates_inline.v --locations-inline --no-templates fixture.cpp -- -std=c++17
  $ cmp no_templates_inline_expected.v no_templates_inline.v
  $ rocq c $ROCQC_ARGS no_templates_inline.v
  $ grep -q 'singleton_msymbol_events : list (name \* indexed_location) := nil' no_templates_inline.v
  $ grep -q 'singleton_mtype_events : list (name \* indexed_location) := nil' no_templates_inline.v

Omitting both location options preserves the existing one-output behavior.

  $ rm -f omitted_locations.v
  $ cpp2v -o omitted.v fixture.cpp -- -std=c++17
  $ rocq c $ROCQC_ARGS omitted.v
  $ test ! -e omitted_locations.v

Invalid CLI combinations fail before opening either requested final path.

  $ cpp2v --locations-all-files fixture.cpp -- -std=c++17 2>&1
  cpp2v: --locations-all-files requires --locations
  [1]
  $ cpp2v --locations-inline fixture.cpp -- -std=c++17 2>&1
  cpp2v: --locations-inline requires --module/-o
  [1]
  $ rm -f conflicting_ast.v conflicting_locations.v
  $ cpp2v --module conflicting_ast.v --locations conflicting_locations.v --locations-inline fixture.cpp -- -std=c++17 2>&1
  cpp2v: --locations and --locations-inline are mutually exclusive
  [1]
  $ test ! -e conflicting_ast.v
  $ test ! -e conflicting_locations.v
  $ cpp2v --locations missing_module_locations.v fixture.cpp -- -std=c++17 2>&1
  cpp2v: --locations requires --module/-o
  [1]
  $ test ! -e missing_module_locations.v
  $ cpp2v --module dash_locations_ast.v --locations - fixture.cpp -- -std=c++17 2>&1
  cpp2v: --locations must name a file (not '-')
  [1]
  $ test ! -e dash_locations_ast.v
  $ cpp2v --module - --locations dash_module_locations.v fixture.cpp -- -std=c++17 2>&1
  cpp2v: --module must name a file when --locations is used
  [1]
  $ test ! -e dash_module_locations.v
  $ cpp2v --module same.v --locations same.v fixture.cpp -- -std=c++17 2>&1
  cpp2v: --module and --locations paths must differ
  [1]
  $ test ! -e same.v
  $ cpp2v --module interactive_ast.v --locations interactive_locations.v --for-interactive Test fixture.cpp -- -std=c++17 2>&1
  cpp2v: --locations is incompatible with --for-interactive
  [1]
  $ test ! -e interactive_ast.v
  $ test ! -e interactive_locations.v
  $ cpp2v --module inline_interactive.v --locations-inline --for-interactive Test fixture.cpp -- -std=c++17 2>&1
  cpp2v: --locations-inline is incompatible with --for-interactive
  [1]
  $ test ! -e inline_interactive.v
  $ cpp2v -o explicit_false.v --locations-inline=false fixture.cpp -- -std=c++17
  $ cmp omitted.v explicit_false.v
  $ test ! -e explicit_false_locations.v

Inline output has one publication transaction. An output open failure publishes
neither a final file nor a `.partial` file.

  $ rm -rf missing_inline_directory
  $ cpp2v --module missing_inline_directory/inline.v --locations-inline fixture.cpp -- -std=c++17 > inline_open_failure.log 2>&1; echo $?
  1
  $ grep -q 'missing_inline_directory/inline.v.partial' inline_open_failure.log
  $ test ! -e missing_inline_directory/inline.v
  $ test ! -e missing_inline_directory/inline.v.partial

A separate location open failure may leave the already-published AST, as
specified, but never publishes the companion's final name.

  $ rm -rf missing_directory
  $ cpp2v --module open_failure_ast.v --locations missing_directory/locations.v fixture.cpp -- -std=c++17 > open_failure.log 2>&1; echo $?
  1
  $ grep -q 'missing_directory/locations.v.partial' open_failure.log
  $ test -f open_failure_ast.v
  $ test ! -e missing_directory/locations.v

The proof-backed construction boundary rejects incompatible events rather than
exporting a fake map, and therefore leaves no compiled companion.

  $ rocq c $ROCQC_ARGS incompatible_companion.v > incompatible.log 2>&1; echo $?
  1
  $ grep -q 'source-location construction failed' incompatible.log
  $ test ! -e incompatible_companion.vo
