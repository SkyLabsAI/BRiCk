  $ . ../setup-project.sh
  $ . ../setup-cpp2v.sh

The test-only Clang probe checks semantic relations under both supported C++
standards, never raw Clang encodings or implementation-specific numeric IDs.
Each extraction is repeated and its complete production serialization compared.

  $ CRAM_CXXFLAGS="-I. -isystem system"
  $ check_cpp2v_source_info_probe_versions test.cpp 17 20
  ../../build-dune-tests/cpp2v-source-info-probe test.cpp --rocq-output test_17_source_values.v -- -std=c++17 -I. -isystem system
  points: valid and invalid projections
  ranges: token character partial cross-file and incompatible same-file macro normalization
  files: exact first-seen include ancestry and distinct same-named buffers
  line-directive: physical differs from logical.cpp:700
  macros: exact nearest-first nested argument body and header frames
  declarations: function member-record member-enum POIs separated
  origins: exact explicit implicit transformed synthesized and inherited edges
  types: TypeSourceInfo written; QualType policy explicit
  rocq-values: all source files and origins faithfully emitted
  ../../build-dune-tests/cpp2v-source-info-probe test.cpp --rocq-output test_17_source_values_repeat.v -- -std=c++17 -I. -isystem system > test_17_source_values_repeat.log
  cmp test_17_source_values.v test_17_source_values_repeat.v
  rocq c -w -notation-overridden -w -notation-incompatible-prefix test_17_source_values.v
  ../../build-dune-tests/cpp2v-source-info-probe test.cpp --rocq-output test_20_source_values.v -- -std=c++20 -I. -isystem system
  points: valid and invalid projections
  ranges: token character partial cross-file and incompatible same-file macro normalization
  files: exact first-seen include ancestry and distinct same-named buffers
  line-directive: physical differs from logical.cpp:700
  macros: exact nearest-first nested argument body and header frames
  declarations: function member-record member-enum POIs separated
  origins: exact explicit implicit transformed synthesized and inherited edges
  types: TypeSourceInfo written; QualType policy explicit
  rocq-values: all source files and origins faithfully emitted
  ../../build-dune-tests/cpp2v-source-info-probe test.cpp --rocq-output test_20_source_values_repeat.v -- -std=c++20 -I. -isystem system > test_20_source_values_repeat.log
  cmp test_20_source_values.v test_20_source_values_repeat.v
  rocq c -w -notation-overridden -w -notation-incompatible-prefix test_20_source_values.v

Text checks ensure the generated companion uses compact indexed tables, inline
or table-referenced macro frames, and source-map construction that never eagerly
decodes provenance.

  $ grep -q 'Encoded.Build_indexed_table' test_17_source_values.v
  $ grep -q 'Encoded.Build_encoded_presumed_point' test_17_source_values.v
  $ grep -q 'Encoded.EncodedRawRange' test_17_source_values.v
  $ grep -q 'Encoded.Build_encoded_origin' test_17_source_values.v
  $ grep -q 'Encoded.InlineMacroFrame' test_17_source_values.v
  $ ! grep -q 'Encoded.MacroFrameReference' test_17_source_values.v
  $ grep -q 'Construction.build_lazy_compact_indexed_dag_source_map_or_fail' test_17_source_values.v
  $ grep -q 'Encoded.Build_indexed_location_dag' test_17_source_values.v
  $ grep -q 'singleton_root_events : singleton_root_locations' test_17_source_values.v
  $ grep -q 'residual_root_events : list Construction.indexed_located_root_event' test_17_source_values.v
  $ grep -q 'compact root events: 0 selected; 0 singleton; 0 residual' test_17_source_values.v
  $ ! grep -Eq 'Construction\.LESymbol|\(LocNode |source_origins : list source_origin|Build_source_origin|presumed_file :=|macro_name :=|origin_class :=' test_17_source_values.v

Proof checks establish that files remain directly available and that the explicit,
eager diagnostic materializer retains complete origins for focused assertions.

  $ rocq c $ROCQC_ARGS check_17.v
  $ rocq c $ROCQC_ARGS check_20.v

A pure boundary fixture forces table cardinalities immediately below, at, and
above 4096 rows, an exact second chunk, and a partial third chunk. It also makes
long repeated macro frames strictly favor references. Compiling both the value
and its independent checker locks direct-array separators/defaults, the two
profitability outcomes (the ordinary probe is inline), exact parsed table sizes,
and first/last decoded values.

  $ ../cpp2v-unit-tests-boundary --emit-indexed-boundary indexed_boundary_values.v
  $ grep -q 'Encoded.MacroFrameReference' indexed_boundary_values.v
  $ ! grep -q 'Encoded.InlineMacroFrame' indexed_boundary_values.v
  $ grep -q 'Encoded.Build_indexed_location_dag' indexed_boundary_values.v
  $ ! grep -q '(LocNode ' indexed_boundary_values.v
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix indexed_boundary_values.v
  $ rocq c $ROCQC_ARGS check_indexed_boundary.v
