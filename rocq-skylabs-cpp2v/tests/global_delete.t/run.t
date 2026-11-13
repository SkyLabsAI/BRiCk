  $ setup_project

cpp2v records whether a delete-expression was written <<::delete>>
(https://eel.is/c++draft/expr.delete#8). Both forms below resolve to the same
global deallocation function, so only the flag tells them apart.

  $ cpp2v --module=test_cpp.v --templates=test_templates_cpp.v test.cpp -- -target x86_64-linux-gnu -std=c++17 -nostdinc
  $ grep -o "E[a-z_]*delete [a-z]* [a-z]*" test_cpp.v test_templates_cpp.v
  test_cpp.v:Edelete false false
  test_cpp.v:Edelete false true
  test_cpp.v:Edelete true false
  test_cpp.v:Edelete true true
  test_cpp.v:Eunresolved_delete false true
  test_templates_cpp.v:Eunresolved_delete false true
  $ dune build test_cpp.vo
