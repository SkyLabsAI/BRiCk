An `extern "C"` name or an asm label that starts with `_Z` can be the symbol
of another C++ entity under its Itanium mangling, so cpp2v refuses the whole
translation unit.

  $ cpp2v -o extern_c_cpp.v extern_c.cpp -- -std=c++17 2>&1 | grep -o 'error: .*'
  error: an `extern "C"` name that starts with `_Z` may name the symbol of another C++ entity
  [1]
  $ cpp2v -o extern_c_var_cpp.v extern_c_var.cpp -- -std=c++17 2>&1 | grep -o 'error: .*'
  error: an `extern "C"` name that starts with `_Z` may name the symbol of another C++ entity
  [1]
  $ cpp2v -o label_cpp.v label.cpp -- -std=c++17 2>&1 | grep -o 'error: .*'
  error: an asm label that starts with `_Z` may name the symbol of another C++ entity
  [1]

Other names and labels are accepted.

  $ cpp2v -o plain_cpp.v plain.cpp -- -std=c++17
