Declaration conditions now have their own Sfor slot. Preserve both the
shadowed and unshadowed condition bindings, as well as ordinary conditions.
The for_condition_support test checks their generated ASTs and lifetimes.

  $ cpp2v -o test_cpp.v test.cpp -- -std=c++17
  $ grep -o '(Sfor' test_cpp.v
  (Sfor
  (Sfor
  (Sfor
  $ if grep -q 'Sunsupported' test_cpp.v; then echo 'unexpected unsupported statement'; exit 1; fi
