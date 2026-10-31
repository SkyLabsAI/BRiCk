Bitfield glvalues must never become ordinary member accesses, even though
their enclosing class now has size and destructor metadata.

  $ cpp2v -vv -check-types -no-elaborate -no-sharing -o test_cpp.v test.cpp -- -std=c++17 2> diagnostics.txt
  $ rocq c ${CHECK_CPP2V_ROCQC_ARGS} test_cpp.v
  $ grep -q 'warning: unsupported expression: bitfield access' diagnostics.txt
  $ sed -n '/(Dfunction .* "read" /,/(Dfunction .* "write" /p' test_cpp.v | grep -Fq '(Eunsupported "MemberExpr"'
  $ sed -n '/(Dfunction .* "write" /,/(Dfunction .* "update" /p' test_cpp.v | grep -Fq '(Eunsupported "BinaryOperator"'
  $ grep -Fq '(Eunsupported "ConditionalOperator"' test_cpp.v
  $ grep -Fq '(Eunsupported "DeclRefExpr"' test_cpp.v
  $ grep -F '(Field (field_name.Id ' test_cpp.v
  [1]

The same guard applies to Clang-generated copy/move bodies.

  $ cpp2v -check-types -no-sharing -o elaborated_cpp.v test.cpp -- -std=c++17
  $ rocq c ${CHECK_CPP2V_ROCQC_ARGS} elaborated_cpp.v
  $ grep -E '\(Field \(field_name.Id "(some_bit|some_other_bit|bits)"' elaborated_cpp.v
  [1]
