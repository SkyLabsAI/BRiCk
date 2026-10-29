Ordinary output isolates field naming from template capture expressions.
  $ cpp2v -check-types -o test.v test.cpp -- -std=gnu++17 2>cpp2v.log
Clang may interleave named captures with the hidden bounds; both bounds
must still receive distinct anonymous names.
  $ grep -o 'field_name.Anon [0-9]*' test.v | sort -u | awk 'END { print NR }'
  2
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix test.v
