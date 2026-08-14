#include "user_header.hpp"
#include <system_header.hpp>

int nested_macro(int value) { return USER_OUTER(value); }

#line 700 "logical.cpp"
int line_mapped(int value) { return value + 3; }
