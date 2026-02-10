CPPFLAGS = -std=c++20
CPP2VFLAGS = --check-types --no-elaborate

CPP_FILES = $(shell find . -name '*.cpp')
HPP_FILES = $(shell find . -name '*.hpp')

GEN_FILES = \
  $(CPP_FILES:.cpp=_cpp.v) $(CPP_FILES:.cpp=_cpp_names.v) \
  $(HPP_FILES:.hpp=_hpp.v) $(HPP_FILES:.hpp=_hpp_names.v)

Q = @

all: $(GEN_FILES) $(GEN_VALCAT_FILES)

%_cpp.v: %.cpp
	$(Q)cpp2v -v -o $@ $< $(CPP2VFLAGS) -- $(CPPFLAGS)
%_hpp.v: %.hpp
	$(Q)cpp2v -v -o $@ $< $(CPP2VFLAGS) -- $(CPPFLAGS)

%_cpp_names.v: %.cpp
	$(Q)cpp2v -v -names $@ $< $(CPP2VFLAGS) -- $(CPPFLAGS)
%_hpp_names.v: %.hpp
	$(Q)cpp2v -v -names $@ $< $(CPP2VFLAGS) -- $(CPPFLAGS)
