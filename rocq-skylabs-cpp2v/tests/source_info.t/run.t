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

Text checks ensure values that the former hand-written probe serializer dropped
remain present in the compact direct-constructor output.

  $ grep -q 'Build_presumed_point "logical.cpp"' test_17_source_values.v
  $ grep -q 'Build_macro_frame (Some "INNER_MACRO")' test_17_source_values.v
  $ grep -q 'Build_macro_frame (Some "HEADER_MACRO")' test_17_source_values.v
  $ grep -q 'Build_source_range (Some' test_17_source_values.v
  $ grep -q 'Build_source_origin' test_17_source_values.v
  $ grep -Eq '\(Some [0-9]+\) \([0-9]+ :: nil\)\)' test_17_source_values.v
  $ ! grep -Eq 'presumed_file :=|macro_name :=|origin_class :=' test_17_source_values.v

Proof checks establish that both complete tables are nonempty and that whole-map
construction, including every anchor and derivation reference, succeeds.

  $ rocq c $ROCQC_ARGS check_17.v
  $ rocq c $ROCQC_ARGS check_20.v
