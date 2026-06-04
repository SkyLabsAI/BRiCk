  $ mkdir out.v.partial
  $ cpp2v -q -o out.v test.cpp -- -std=c++17 2>&1
  out.v.partial: Is a directory
  [1]
  $ test ! -e out.v
