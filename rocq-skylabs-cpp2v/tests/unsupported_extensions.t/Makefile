# Each source needs its own flags to enable its extension. [named.cpp] is
# checked by [named.sh] instead, since clang before 22 rejects its flag.
Q = @

all: asm_cpp.v coro_cpp.v

named_cpp.v: named.cpp
	$(Q)cpp2v -v -o $@ $< --check-types -- -std=c++23 -Xclang -fnamed-loops

asm_cpp.v: asm.cpp
	$(Q)cpp2v -v -o $@ $< --check-types -- -std=c++20

coro_cpp.v: coro.cpp
	$(Q)cpp2v -v -o $@ $< --check-types -- -std=c++20
