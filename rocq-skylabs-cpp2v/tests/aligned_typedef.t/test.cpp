typedef int X __attribute__((aligned(16)));
typedef unsigned short u16a __attribute__((aligned(1)));

// What Clang computes.
static_assert(sizeof(X) == 4 && alignof(X) == 16, "over-aligned typedef");
static_assert(sizeof(u16a) == 2 && alignof(u16a) == 1, "under-aligned typedef");

unsigned long a_over() { return alignof(X); }
unsigned long a_under() { return alignof(u16a); }
unsigned long a_ref() { return alignof(X &); }
unsigned long a_plain() { return alignof(int); }
unsigned long s_over() { return sizeof(X); }
X v;
unsigned long a_var() { return alignof(v); } // GNU extension

// Arrays of unknown bound, and enumerations with an alignment attribute: BRiCk
// aligns an enumeration like its underlying type.
typedef long long L4 __attribute__((aligned(4)));
extern L4 arr_inc[];
unsigned long a_inc() { return alignof(L4[]); }
enum __attribute__((aligned(8))) E8 : char { e0 };
enum __attribute__((aligned(1))) E1 : int { e1 };
unsigned long a_e8() { return alignof(E8); }
unsigned long a_e1() { return alignof(E1); }

// The size of X is not a multiple of its alignment, so stepping an X* by
// one element leaves a pointer that is not aligned for X. BRiCk sees an int*.
X *step(X *p) { return p + 1; }

struct __attribute__((packed)) P {
    char c;
    int i;
    const short s;
    unsigned long long a[2];
};
#pragma pack(push, 2)
struct Q { char c; int i; };
#pragma pack(pop)
struct U { char c; u16a u; };
struct SE { char c; E1 e; };
#pragma pack(push, 4)
struct SE8 { int a; E8 e; };
#pragma pack(pop)
struct S { int i; };
struct __attribute__((packed)) R { char c; S s; };

// Variables of an under-aligned typedef are only as aligned as the typedef.
u16a g_under;
X g_over;
unsigned short local_under() { char c = 0; u16a x = 1; (void)c; return x; }

// Parameters of an under-aligned type: the function is unsupported.
unsigned short param_under(char c, u16a p) { (void)c; return p; }
// Under-aligned variables BRiCk cannot type: unsupported types.
struct S2 { int x; };
typedef S2 US2 __attribute__((aligned(1)));
US2 g_rec;
extern u16a g_inc[];
// Structured bindings hold an under-aligned variable.
int bind() { u16a arr[1] = {3}; auto [x] = arr; return x; }

// Accesses to a packed field: reads and assignments used as statements are
// printed at the field's Trealigned type; other uses are unsupported.
int read_i(P *p) { return p->i; }
void write_i(P *p) { p->i = 5; }
int *addr_i(P *p) { return &p->i; }
int &ref_i(P *p) { return p->i; }
void inc_i(P *p) { p->i += 1; }
int chain_i(P *p) { return p->i = 3; }
