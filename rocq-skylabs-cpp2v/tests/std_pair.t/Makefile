CPPFLAGS = -std=gnu++23

CPP_FILES = $(shell find . -name '*.cpp')

GEN_FILES = \
  $(CPP_FILES:.cpp=_cpp.v)

Q = @

all: $(GEN_FILES)

%_cpp.v: %.cpp
	$(Q)cpp2v -v -o $@ $< --check-types --no-elaborate -- $(CPPFLAGS)
