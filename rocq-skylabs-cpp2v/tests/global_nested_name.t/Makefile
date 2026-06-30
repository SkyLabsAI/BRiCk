CPPFLAGS = -std=c++17

Q = @

all: test_cpp.v

test_cpp.v: test.cpp
	$(Q)cpp2v -v -o $@ $< --check-types -- $(CPPFLAGS)
