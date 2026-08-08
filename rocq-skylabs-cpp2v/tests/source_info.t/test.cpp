#include "user_header.hpp"
#include <system_header.hpp>

#line 700 "logical.cpp"
int line_mapped = 1;
#line 8 "test.cpp"

#define INNER_MACRO(x) ((x) + 1)
#define OUTER_MACRO(x) INNER_MACRO(x)
#define PASS_MACRO(x) x
#define LEFT_MACRO 10
#define RIGHT_MACRO 20
#define BODY_INNER_MACRO 31
#define BODY_OUTER_MACRO BODY_INNER_MACRO

int nested_macro = OUTER_MACRO(PASS_MACRO(3));
int header_value = HEADER_MACRO(PASS_MACRO(4));
int incompatible_macros = LEFT_MACRO + RIGHT_MACRO;
int nested_body_macro = BODY_OUTER_MACRO;

template <class T> T id(T value) { return value; }
int instantiated = id(5);

template <class T> struct MemberHolder {
  struct Nested {};
  enum MemberEnum { MemberValue };
};
MemberHolder<int>::Nested instantiated_member;
MemberHolder<int>::MemberEnum instantiated_enum =
    MemberHolder<int>::MemberValue;

int typed_value = 6;
