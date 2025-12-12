
// `char`
auto c0 = 'A';        // char
auto c0_big = '\xff'; // char

// `wchar_t`
static_assert(sizeof(wchar_t) == 4 * sizeof(char), "wchar is 32-bits");
auto wc = L'A';
auto wc_med = L'\xffff';
auto wc_big = L'\xffffffff';

// `char16_t`
auto c16 = u'A';
auto c16_med = u'\xfff';
auto c16_big = u'\xffff';

// `char32_t`
auto c32 = U'A';
auto c32_med = U'\xffff';
auto c32_big = U'\xffffffff';

#if 202002L <= __cplusplus 
auto c8 = u8'A';
auto c8_big = u8'\xff';
#endif

int x = 'a';
