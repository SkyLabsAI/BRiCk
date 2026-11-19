A case label that is not directly in the switch block is printed inside its own
block, so the output type-checks; `supported` rejects the switch.
  $ check_cpp2v test.cpp
  cpp2v -v -check-types -o test_17_cpp.v test.cpp -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix test_17_cpp.v
  $ grep -A3 'Sif None None' test_17_cpp.v | grep -o 'Sseq (\|Scase'
  Sseq (
