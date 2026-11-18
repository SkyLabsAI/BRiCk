typedef int X32 __attribute__((aligned(32)));

// Clang loads and stores through a pointer or reference to an over-aligned
// type with that type's alignment, and the optimizer relies on it, while X32*
// and int* are the same type. Such accesses, member accesses through such a
// pointer and builtin calls on one are unsupported.
struct S3 { int a; int b; };
typedef S3 S64 __attribute__((aligned(64)));
int deref_over(int *q) { X32 *p = q; return *p; }
int index_over(X32 *p) { return p[1]; }
void store_over(X32 &r) { r = 1; }
int arrow_over(S64 *p) { return p->b; }
void copy_over(X32 *d, const int *s) { __builtin_memcpy(d, s, 4); }
// Clang takes the alignment of an array, incomplete or void typedef from the
// attribute.
typedef int A8[8] __attribute__((aligned(32)));
int arr_over(A8 *pa) { return (*pa)[0]; }
typedef void V64 __attribute__((aligned(64)));
void void_over(V64 *d, const void *s) { __builtin_memcpy(d, s, 4); }
// A variable declared more aligned than its definition, or not defined here.
int g_plain;
extern X32 g_plain;
int redecl_over() { return g_plain; }
extern X32 g_ext;
int extern_over() { return g_ext; }
extern int g_gnu __attribute__((aligned(32)));
int gnu_over() { return g_gnu; }
// Clang looks through implicit derived-to-base conversions, and takes the
// alignment of a member call's object from the pointer.
struct B4 { int x; virtual int f(); };
struct D4 : B4 { int z; };
typedef D4 D64 __attribute__((aligned(64)));
int base_over(D64 *p) { return p->x; }
int vcall_over(D64 *p) { return p->f(); }
// A by-value parameter only has the ABI's alignment, which Clang does not
// trust inside a lambda capturing it by reference.
struct L8 { long a[8]; };
typedef L8 L64 __attribute__((aligned(64)));
long capture_over(L64 s) { return [&] { return s.a[0]; }(); }
// A weak definition may be replaced by a less aligned one.
X32 g_weak __attribute__((weak));
int weak_over() { return g_weak; }
// Clang loads a virtual base's offset, and the vtable or array cookie of a
// deleted object, at the alignment of the pointer's type.
struct VB { int x; };
struct VD : virtual VB { int z; };
typedef VD VD64 __attribute__((aligned(64)));
VB *vbase_over(VD64 *p) { return p; }
struct W { long a; ~W(); };
typedef W W16 __attribute__((aligned(16)));
void delete_over(W16 *p) { delete[] p; }

// Supported: Clang allocates variables and temporaries and lays out records.
X32 g_def;
int def_over() { return g_def; }
int var_over() { X32 x = 1; x += 2; return x; }
struct HasX { X32 x; };
int field_over(HasX *h) { return h->x; }
int field_ref_over(HasX &h) { h.x = 3; return h.x; }
void atomic_var() { __atomic_store_n(&g_def, 1, __ATOMIC_SEQ_CST); }
// C++ requires the definition of an alignas variable to repeat the alignas.
alignas(32) extern int g_alignas;
int alignas_ok() { return g_alignas; }
S64 make_s64();
int temp_over() { return make_s64().a; }
int bind_over(HasX &h) { auto &[x] = h; return x; }
