  $ . ../setup-project.sh

cpp2v should report the ABI selected by the requested clang target, not the
host platform running the test. This is observable on aarch64-linux because
both plain char and wchar_t are unsigned there, while x86_64-linux uses signed
plain char and signed wchar_t.

  $ cpp2v --module=x64.v test.cpp -- -target x86_64-linux-gnu -std=c++17
  $ cpp2v --module=aarch64.v test.cpp -- -target aarch64-linux-gnu -std=c++17
  $ dune build check.vo
