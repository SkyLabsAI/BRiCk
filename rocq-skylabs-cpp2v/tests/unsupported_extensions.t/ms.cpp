// MS extensions (-fms-extensions -fms-compatibility, on the Linux target
// that cpp2v supports). `__if_exists` is resolved by the parser and `__super`
// is an ordinary qualified call; `__uuidof` and properties print unsupported;
// `__noop` and `__assume` do not evaluate their arguments. The jump past an
// initialized declaration is accepted by MS compatibility and printed as
// an ordinary `goto`, which the logic does not resolve. The `__unaligned`
// qualifier prints as an unsupported type.
struct _GUID { unsigned long a; unsigned short b, c; unsigned char d[8]; };
struct __declspec(uuid("12345678-1234-1234-1234-123456789abc")) I {};
struct P { int g() { return 1; } void s(int) {} __declspec(property(get = g, put = s)) int prop; };
struct B { virtual int v() { return 1; } };
struct D : B { int v() override { return __super::v(); } };
int ms_if_exists() { int r = 0; __if_exists(B) { r = 1; } __if_not_exists(Zzz) { r += 2; } return r; }
const void *ms_uuidof() { return &__uuidof(I); }
int ms_prop(P &p) { p.prop = 3; return p.prop; }
int ms_noop() { __noop(1, 2); return 0; }
int ms_assume(int x) { __assume(x > 0); return x; }
int ms_jump(int c) { if (c) goto L; int x = 5; L: return 0; }
// clang marks the arguments of `__builtin_constant_p` unevaluated as well.
int const_p(int x) { return __builtin_constant_p(x++); }
int unaligned_read(int __unaligned *p) { return *p; }
