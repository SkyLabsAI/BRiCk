Default/local location arrays and indices are deterministic.

  $ cpp2v test.cpp -o test_1.v --
  $ cpp2v test.cpp -o test_2.v --
  $ diff test_1.v test_2.v
  $ grep -q 'LocInfo' test_1.v
  $ grep -q 'Definition file_names' test_1.v
  $ grep -q 'Definition loc_table' test_1.v

Legacy-shaped none output is deterministic and contains no location artifacts.

  $ cpp2v --loc-info=none test.cpp -o none_1.v --
  $ cpp2v --loc-info=none test.cpp -o none_2.v --
  $ diff none_1.v none_2.v
  $ if grep -E '([A-Z]+LocInfo|file_names|loc_table|Stdlib.Array.PArray|PrimInt63|syntax.loc_info|array_scope|uint63_scope)' none_1.v; then exit 1; fi
