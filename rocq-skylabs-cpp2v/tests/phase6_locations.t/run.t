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
  $ test ! -e fixture_17_cpp.v.partial
  $ test ! -e fixture_17_cpp_locations.v.partial

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

Suppressing templates also suppresses both template location maps while the two
outputs remain valid.

  $ cpp2v -o no_templates.v --locations no_templates_locations.v --no-templates fixture.cpp -- -std=c++17
  $ rocq c $ROCQC_ARGS no_templates.v
  $ rocq c $ROCQC_ARGS no_templates_locations.v
  $ rocq c $ROCQC_ARGS no_templates_check.v
  $ ! grep -q 'Construction.LEM' no_templates_locations.v

Omitting --locations preserves the existing one-output behavior.

  $ rm -f omitted_locations.v
  $ cpp2v -o omitted.v fixture.cpp -- -std=c++17
  $ rocq c $ROCQC_ARGS omitted.v
  $ test ! -e omitted_locations.v

Invalid CLI combinations fail before opening either requested final path.

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

A location open failure may leave the already-published AST, as specified, but
never publishes the companion's final name.

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
