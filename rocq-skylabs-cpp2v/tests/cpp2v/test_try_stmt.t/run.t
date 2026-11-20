Under BRiCk's non-throwing semantics, cpp2v lowers `try B catch ... H` to `B`.
test.v checks that each `try` function lowers to the body of a twin without
`try`, so the try-block is kept and the handlers are dropped.

  $ setup_project
  $ cpp2v -check-types -o test_cpp.v test.cpp -- -std=c++17
  $ dune build

No `try` survives as an unsupported statement, while a `throw` inside a
try-block stays unsupported, in try_throw as in ref_throw.

  $ grep -Eo '(Sunsupported|Eunsupported) "[^"]*"' test_cpp.v
  Eunsupported "CXXThrowExpr"
  Eunsupported "CXXThrowExpr"
