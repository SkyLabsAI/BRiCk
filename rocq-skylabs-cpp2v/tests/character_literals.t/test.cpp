char high_char() { return '\xff'; }
char ascii_char() { return 'A'; }
char8_t utf8_char() { return u8'\xff'; }
char16_t utf16_char() { return u'\xffff'; }
char32_t utf32_char() { return U'\U0001f642'; }
wchar_t wide_char() { return L'\xffff'; }
int multichar() { return 'AB'; }
int negative_multichar() { return '\xff\xff\xff\xff'; }
