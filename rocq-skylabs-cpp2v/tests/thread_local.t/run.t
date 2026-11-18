BRiCk has no thread-local storage: each use of a `thread_local` or `__thread`
variable prints as `Eunsupported`. The declarations stay ordinary variables.
  $ CRAM_CPP2VFLAGS=--no-sharing check_cpp2v test.cpp
  cpp2v -v -check-types -o test_17_cpp.v test.cpp --no-sharing -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp.v
  $ grep -o 'Eunsupported "[^"]*"\|Eglobal (Nglobal (Nid "[a-z_]*"))' test_17_cpp.v
  Eunsupported "thread_local variable"
  Eunsupported "thread_local variable"
  Eglobal (Nglobal (Nid "plain"))
  Eunsupported "thread_local variable"
  $ grep -o 'Dvariable (Nglobal (Nid "[a-z_]*"))' test_17_cpp.v
  Dvariable (Nglobal (Nid "tls"))
  Dvariable (Nglobal (Nid "gnu_tls"))
  Dvariable (Nglobal (Nid "plain"))
