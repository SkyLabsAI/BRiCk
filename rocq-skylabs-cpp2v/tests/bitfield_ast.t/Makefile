CPPFLAGS = -std=c++20

Q = @

all: test_cpp.v base_cpp.v

test_cpp.v: test.cpp
	$(Q)cpp2v -v -o $@ $< --check-types -- $(CPPFLAGS)
base_cpp.v: base.cpp
	$(Q)cpp2v -v -o $@ $< -- $(CPPFLAGS)
