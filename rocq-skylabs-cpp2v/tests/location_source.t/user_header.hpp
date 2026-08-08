#pragma once
#define USER_INNER(value) ((value) + 1)
#define USER_OUTER(value) USER_INNER(value)
inline int user_header_value() { return 5; }
