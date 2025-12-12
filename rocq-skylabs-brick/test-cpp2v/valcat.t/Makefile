CPPFLAGS = -std=c++17

CPP_FILES = $(shell find . -name '*.cpp')
HPP_FILES = $(shell find . -name '*.hpp')

GEN_FILES = \
  $(CPP_FILES:.cpp=_cpp.v) $(CPP_FILES:.cpp=_cpp_names.v) \
  $(HPP_FILES:.hpp=_hpp.v) $(HPP_FILES:.hpp=_hpp_names.v)

VALCAT_VERS = 11 14 17 20
GEN_VALCAT_FILES = $(foreach v,$(VALCAT_VERS),valcat_of_$(v)_cpp.v)

Q = @

all: $(GEN_FILES) $(GEN_VALCAT_FILES)

valcat_of_%_cpp.v: valcat_of.cpp
	$(Q)cpp2v -v -o $@ $< -- -std=c++$*

%_cpp.v: %.cpp
	$(Q)cpp2v -v -o $@ $< -- $(CPPFLAGS)
%_hpp.v: %.hpp
	$(Q)cpp2v -v -o $@ $< -- $(CPPFLAGS)

%_cpp_names.v: %.cpp
	$(Q)cpp2v -v -names $@ $< -- $(CPPFLAGS)
%_hpp_names.v: %.hpp
	$(Q)cpp2v -v -names $@ $< -- $(CPPFLAGS)
