  $ setup_project

cpp2v emits an aligned allocation function referring to std::align_val_t, but
omits the corresponding enum declaration from the translation unit.

  $ cpp2v --module=test_cpp.v test.cpp -- -std=c++17 -nostdinc
  $ dune build check.vo
       = None
       : option GlobDecl
