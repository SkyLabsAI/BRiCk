CPPFLAGS = -std=c++17

GEN_FILES = cases_cpp.v

Q = @

all: $(GEN_FILES)

cases_cpp.v: cases.cpp
	$(Q)cpp2v -v -o $@ $< --check-types -- $(CPPFLAGS)
