CPPFLAGS = -std=c++17

CPP_FILES = $(shell find . -name '*.cpp')
HPP_FILES = $(shell find . -name '*.hpp')

GEN_FILES = $(CPP_FILES:.cpp=_cpp.v) $(HPP_FILES:.hpp=_hpp.v)

Q = @

all: $(GEN_FILES) inc_noelab_hpp.v

# Without elaboration, unused implicit members stay [Some Defaulted].
inc_noelab_hpp.v: inc.hpp
	$(Q)cpp2v -v --no-elaborate -o $@ $< -- $(CPPFLAGS)

%_cpp.v: %.cpp
	$(Q)cpp2v -v -o $@ $< -- $(CPPFLAGS)
%_hpp.v: %.hpp
	$(Q)cpp2v -v -o $@ $< -- $(CPPFLAGS)
