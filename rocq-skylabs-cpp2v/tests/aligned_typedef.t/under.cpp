// Under-aligned typedefs of over-aligned types: Clang allocates temporaries
// and plain-new storage at the typedef's alignment, below the alignment BRiCk
// assumes for the erased type.
struct alignas(32) S {
    char x;
    S() : x(0) {}
    S(char c) : x(c) {}
};
typedef S U __attribute__((aligned(1)));
typedef int I1 __attribute__((aligned(1)));

unsigned long low(const U &r) { return (unsigned long)&r % alignof(S); }
int take(const int &r) { return r; }
U make();

// Rejected: under-aligned temporaries and plain new of an under-aligned type
// whose erased type needs more than the default new alignment.
unsigned long temp_rec() { return low(U{7}); }
char member_temp() { return make().x; }
int temp_int() { return take(I1(5)); }
U *new_rec() { return new U; }
void del_rec(U *p) { delete p; }

// Rejected: discarded prvalues of such a class type, which Clang initializes
// in a slot at the typedef's alignment, with no MaterializeTemporaryExpr.
void discard_call() { make(); }
void discard_ctor() { U(); }
void discard_comma() { (void)(U(), 0); }
void discard_cond(bool b) { b ? make() : make(); }

// Supported.
int *new_int() { return new I1(1); }
S *new_s() { return new S; }
unsigned long temp_s() { return low(S{7}); }
