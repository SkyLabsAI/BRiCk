Condition declarations retain their own optional field in the loop AST.
Compile the generated Rocq checks as well as the C++ lifetime oracle.

  $ setup_project
  $ cpp2v -check-types -o test_cpp.v test.cpp -- -std=c++17
  $ grep -Eo '\(Sfor([[:space:]]|$)' test_cpp.v | wc -l | tr -d ' '
  9
  $ dune build
  $ clang++ -std=c++17 -DNATIVE_ORACLE test.cpp -o native
  $ ./native
