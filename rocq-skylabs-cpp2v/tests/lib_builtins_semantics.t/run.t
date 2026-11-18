Library builtin rewriting must preserve semantics, including in freestanding
implementations. These regressions come from the adversarial review of
SkyLabsAI/BRiCk#491. They assert the intended translation rather than recording
incorrect calls as accepted output. lib_builtins.t separately checks synthesized
names and declarations.

A freestanding abs implementation can return 7 while explicit __builtin_abs(-3)
returns 3. The C++ static_assert checks the builtin result; the Rocq assertions
check that the builtin call and the ordinary call retain their distinct targets,
and that the translated ordinary function still returns 7.

  $ cpp2v_command --no-sharing -check-types -o freestanding_cpp.v freestanding.cpp -- -std=c++17 -ffreestanding
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix freestanding_cpp.v
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix freestanding.v

Clang's F attribute also covers stack allocation. Even in hosted mode,
__builtin_alloca_with_align must not call the unrelated alloca_with_align
function declared here.

  $ cpp2v_command --no-sharing -check-types -o alloca_cpp.v alloca.cpp -- -std=c++17
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix alloca_cpp.v
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix alloca.v

When a library call is rewritten, an existing C-linkage declaration inside a
namespace must be reused. Otherwise the generated TU demands a second function
symbol even though Clang gives both calls the same linker symbol.

  $ cpp2v_command --no-sharing -check-types -o namespace_cpp.v namespace.cpp -- -std=c++17
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix namespace_cpp.v
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix namespace.v
