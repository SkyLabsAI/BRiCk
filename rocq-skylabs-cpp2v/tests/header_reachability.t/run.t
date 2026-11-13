Translate only the declarations reachable from the main file.

  $ cpp2v_command --no-elaborate --check-types -o test_cpp.v test.cpp -- -std=c++20
  $ grep -E 'DeadRecord|dead_|unrelated assertion|unused_namespace' test_cpp.v
  [1]
  $ for name in UsedRecord used_helper used_function root UsedInlineRecord inline_root; do grep -q "\"$name\"" test_cpp.v || echo "missing $name"; done
  $ grep -c 'Dusing_namespace' test_cpp.v
  1
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix test_cpp.v

An include-only translation unit exposes the included header API.

  $ cpp2v_command --no-elaborate --check-types -o include_only_cpp.v include_only.cpp -- -std=c++20
  $ for name in DeadRecord dead_function UsedRecord used_function; do grep -q "\"$name\"" include_only_cpp.v || echo "missing $name"; done
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix include_only_cpp.v
