# Each source needs its own flags to enable its extension. [named.cpp] is
# checked by [named.sh] instead, since clang before 22 rejects its flag.
Q = @

all:

named_cpp.v: named.cpp
	$(Q)cpp2v -v -o $@ $< --check-types -- -std=c++23 -Xclang -fnamed-loops
