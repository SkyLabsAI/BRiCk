cpp2v looks through the typedef for the element type of the string literal.
  $ check_cpp2v test.cpp
  cpp2v -v -check-types -o test_17_cpp.v test.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp.v
  $ grep -o 'Estring .*' test_17_cpp.v
  Estring (literal_string.Build_t "abc" 1%N) Tchar))).
