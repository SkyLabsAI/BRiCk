  $ setup_project

The default is local mode, and invalid values are rejected.

  $ cpp2v -o default_cpp.v fixture.cpp -- -std=c++17 -I.
  $ cpp2v --loc-info=local -o local_cpp.v fixture.cpp -- -std=c++17 -I.
  $ diff default_cpp.v local_cpp.v
  $ cpp2v --help | grep -A2 -- '--loc-info=' | sed 's/^  *//'
  --loc-info=<value>              - source location information (default: local)
  =none                         -   disable location information
  =local                        -   locations involving the original TU
  $ if cpp2v --loc-info=invalid -o invalid.v fixture.cpp -- -std=c++17 -I. >invalid.log 2>&1; then exit 1; fi
  $ grep -q "Cannot find option named 'invalid'" invalid.log

None mode stays free of location work and output artifacts for every output
shape, with and without sharing.

  $ cpp2v --loc-info=none --no-templates -o none_static_cpp.v fixture.cpp -- -std=c++17 -I.
  $ cpp2v --loc-info=none -o none_combined_cpp.v fixture.cpp -- -std=c++17 -I.
  $ cpp2v --loc-info=none --no-templates -o none_separate_static_cpp.v --templates none_separate_templates_cpp.v fixture.cpp -- -std=c++17 -I.
  $ cpp2v --loc-info=none --no-templates -o none_names_source_cpp.v --name-test none_names_cpp.v fixture.cpp -- -std=c++17 -I.
  $ cpp2v --loc-info=none --no-templates --no-sharing -o none_no_sharing_cpp.v fixture.cpp -- -std=c++17 -I.
  $ if grep -E '([A-Z]+LocInfo|file_names|loc_table|Stdlib.Array.PArray|PrimInt63|syntax.loc_info|array_scope|uint63_scope)' none_*.v; then exit 1; fi
  $ absolute_root=$(pwd -P)
  $ if grep -h -v '(\*' none_*.v | grep -F "$absolute_root"; then exit 1; fi

Local mode emits all supported wrappers and stream-local tables after the AST.

  $ cpp2v --loc-info=local --no-templates -o local_static_cpp.v fixture.cpp -- -std=c++17 -I.
  $ cpp2v --loc-info=local --no-templates -o local_separate_static_cpp.v --templates local_separate_templates_cpp.v fixture.cpp -- -std=c++17 -I.
  $ cpp2v --loc-info=local --no-templates -o local_names_source_cpp.v --name-test local_names_cpp.v fixture.cpp -- -std=c++17 -I.
  $ for ctor in ELocInfo SLocInfo DLocInfo BLocInfo NLocInfo ANLocInfo ALocInfo; do grep -q "$ctor" local_cpp.v || { echo "missing $ctor"; exit 1; }; done
  $ grep -Eq 'NLocInfo [0-9]+%uint63 \(Nscoped \(Ndependent \(Tparam "T"\)\)' local_separate_templates_cpp.v
  $ grep -Eq 'ANLocInfo [0-9]+%uint63 \(Nid "location_member"\)' local_separate_templates_cpp.v
  $ for output in local_cpp.v local_static_cpp.v local_separate_static_cpp.v local_separate_templates_cpp.v local_names_cpp.v; do grep -q 'Definition file_names' "$output"; grep -q 'Definition loc_table' "$output"; done
  $ test "$(grep -n '^Definition source' local_cpp.v | tail -1 | cut -d: -f1)" -lt "$(grep -n '^Definition file_names' local_cpp.v | cut -d: -f1)"
  $ test "$(grep -n '^Definition templates' local_separate_templates_cpp.v | cut -d: -f1)" -lt "$(grep -n '^Definition file_names' local_separate_templates_cpp.v | cut -d: -f1)"
  $ test "$(grep -n '^Definition template_names' local_names_cpp.v | cut -d: -f1)" -lt "$(grep -n '^Definition file_names' local_names_cpp.v | cut -d: -f1)"

Rows and files are first-seen, deduplicated, and bounded by their local arrays.

  $ check_bounds() { output=$1; rows=$(grep -c 'Build_locations' "$output"); files=$(grep -Ec 'PArray.set result [0-9]+%uint63 .*%pstring in$' "$output"); for index in $(grep -oE '[A-Z]+LocInfo [0-9]+' "$output" | awk '{print $2}'); do test "$index" -lt "$rows" || return 1; done; for index in $(grep -oE 'Build_location [0-9]+' "$output" | awk '{print $2}'); do test "$index" -lt "$files" || return 1; done; }
  $ for output in local_cpp.v local_static_cpp.v local_separate_static_cpp.v local_separate_templates_cpp.v local_names_cpp.v; do check_bounds "$output"; done
  $ left_binding_index=$(grep -B1 '(Bbind "left"' local_cpp.v | head -1 | grep -oE '[0-9]+%uint63' | sed 's/%uint63//')
  $ left_expr_index=$(grep -A4 '(Bbind "left"' local_cpp.v | grep -m1 -oE 'ELocInfo [0-9]+' | awk '{print $2}')
  $ test "$left_binding_index" = "$left_expr_index"
  $ test "$(grep -c "PArray.set result ${left_binding_index}%uint63 (Build_locations" local_cpp.v)" = 1

A macro expanded in the main file preserves both the main-file expansion and
header spelling projections. Header-only AST nodes are filtered out.

  $ fixture_path=$(realpath fixture.cpp)
  $ header_path=$(realpath included.hpp)
  $ grep -Fq "$fixture_path" local_cpp.v
  $ grep -Fq "$header_path" local_cpp.v
  $ grep -Eq 'Build_locations \(Build_location 0%uint63[^)]*\) \(Build_location 1%uint63' local_cpp.v
  $ header_name=$(grep -E '^#\[local\] Definition n[0-9]+ .*header_only_location' local_cpp.v | sed -E 's/^#\[local\] Definition (n[0-9]+).*/\1/')
  $ sed -n "/^    (Dfunction ${header_name}$/,/^    (Dstruct/p" local_cpp.v | grep -q 'header_only_location\|Dfunction'
  $ if sed -n "/^    (Dfunction ${header_name}$/,/^    (Dstruct/p" local_cpp.v | grep -q 'LocInfo'; then exit 1; fi
  $ if grep -Eq 'Build_location 1%uint63 [0-9]+%uint63 (5|6|7)%uint63' local_cpp.v; then exit 1; fi

The emitted arrays and defaults type-check in every local output stream.

  $ dune build
