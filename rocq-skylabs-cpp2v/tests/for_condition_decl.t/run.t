A condition declaration cannot be represented by Sfor. Reject both the
shadowing case (which previously read an outer variable) and the unshadowed
case, while preserving ordinary expression conditions.

  $ cpp2v -o test_cpp.v test.cpp -- -std=c++17
  $ grep -o 'Sunsupported "for condition declaration"' test_cpp.v
  Sunsupported "for condition declaration"
  Sunsupported "for condition declaration"
  $ grep -o '(Sfor' test_cpp.v
  (Sfor
