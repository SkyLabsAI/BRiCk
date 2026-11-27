A 1 MB string literal translates and compiles with a small stack
(https://github.com/SkyLabsAI/BRiCk/issues/510: printing one list cell per
byte made Rocq run out of stack). The source is generated in this test.

Pin OCaml 5's stack limit (in words; 1M words = 8 MB on 64-bit) so the result
does not depend on the machine. `ulimit -s` does not affect OCaml 5 stacks.
  $ export OCAMLRUNPARAM=l=1M
  $ { printf 'const char *text() { return "'; printf '%1000000s' '' | tr ' ' a; echo '"; }'; } > test.cpp
  $ check_cpp2v test.cpp
  cpp2v -v -check-types -o test_17_cpp.v test.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp.v
