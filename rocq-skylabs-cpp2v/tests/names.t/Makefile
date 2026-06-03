CPPFLAGS = -std=c++20

CPP_FILES = $(shell find . -name '*.cpp')
HPP_FILES = $(shell find . -name '*.hpp')

GEN_FILES = $(CPP_FILES:.cpp=_cpp.v) $(HPP_FILES:.hpp=_hpp.v)

Q = @

all: $(GEN_FILES) $(GEN_VALCAT_FILES)

%_cpp.v: %.cpp
	$(Q)cpp2v -v -o $@ $< --check-types -- $(CPPFLAGS)
%_hpp.v: %.hpp
	$(Q)cpp2v -v -o $@ $< --check-types -- $(CPPFLAGS)
