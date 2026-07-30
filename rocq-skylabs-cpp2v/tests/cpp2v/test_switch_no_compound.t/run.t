The body of a switch need not be a compound statement. This is not just a
corner case: googletest's GTEST_AMBIGUOUS_ELSE_BLOCKER_ expands to
"switch (0) case 0: default:" and every ASSERT_ and EXPECT_ macro wraps its
body in it, so the form below is what those macros expand to.

  $ . ../../setup-cpp2v.sh
  $ check_cpp2v test.cpp
  cpp2v -v -check-types -o test_17_cpp.v test.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp.v

Such a substatement implicitly defines a block scope, and is as if rewritten as
a compound-statement containing it ([stmt.select]/2), so the AST must be exactly
the one produced for the explicitly braced spelling: the labels land in the list
of the same [Sseq], which is where [wp_switch] looks for them.

  $ check_cpp2v test_braced.cpp
  cpp2v -v -check-types -o test_braced_17_cpp.v test_braced.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix test_braced_17_cpp.v
  $ diff test_17_cpp.v test_braced_17_cpp.v
