CPPFLAGS = -std=c++20 -Wno-vla-cxx-extension

Q = @

all: test_cpp.v

%_cpp.v: %.cpp
	$(Q)cpp2v -v -o $@ $< --check-types -- $(CPPFLAGS)
