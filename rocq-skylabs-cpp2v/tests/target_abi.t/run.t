  $ . ../setup-project.sh

cpp2v should report the ABI selected by the requested clang target, not the
host platform running the test. This is observable on aarch64-linux because
both plain char and wchar_t are unsigned there, while x86_64-linux uses signed
plain char and signed wchar_t.

  $ cpp2v --module=x64.v test.cpp -- -target x86_64-linux-gnu -std=c++17
  $ grep '  abi ' x64.v
    abi (abi.mkT int_rank.Ilong Signed Signed Little)

  $ cpp2v --module=aarch64.v test.cpp -- -target aarch64-linux-gnu -std=c++17
  $ grep '  abi ' aarch64.v
    abi (abi.mkT int_rank.Ilong Unsigned Unsigned Little)
