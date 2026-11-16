// Bit-field metadata of opaque records ([o_bitfields]) and bit-field
// accesses ([Ebitfield]).

struct S {
    int a : 3;      // run "a" = {a, b, u}
    int b : 5;
    unsigned u : 4;
    int plain;      // a non-bit-field member ends a run
    int c : 2;      // run "c" = {c}
    int : 0;        // a zero-width bit-field ends a run
    int d : 4;      // run "d" = {d, e}
    int : 3;        // unnamed padding: part of run "d", no entry
    int e : 1;
};

struct Bad {
    int x : 3;          // run "x" = {x, f}: unsupported, f is a bool
    bool f : 1;
    char sep;
    mutable int m : 2;  // run "m" = {m, k}: unsupported, m is mutable
    int k : 2;
    char sep2;
    unsigned ok : 4;    // run "ok" = {ok}: supported
};

struct Kinds {
    unsigned char n : 4;  // run "n" = {n, s, big}: supported
    signed char s : 3;
    long long big : 40;
    int sep;
    char ch : 3;          // run "ch": unsupported, BRiCk's plain char is not [Vint]
    int sep2;
    int w : 40;           // run "w": unsupported, wider than its type
};

union U {               // bit-fields of unions are unsupported
    unsigned lo : 4;
    unsigned all : 8;
};

int rd(const S &s) { return s.a; }
unsigned rd_arrow(const S *p) { return p->u; }
void wr(S &s, int v) { s.a = v; }
void compound(S &s) { s.b += 3; }
int pre_inc(S &s) { return ++s.a; }
int post_inc(S &s) { return s.a++; }
void comma_wr(S &s, int x) { (x, s.a) = 1; }
void assign_assign(S &s) { (s.a = 1) = 2; }
int cond_rd(S &s, int &x, bool c) { return c ? s.a : x; }
void cond_wr(S &s, int &x, bool c) { (c ? s.a : x) = 9; }
void discard(S &s) { s.a; }
int rd_bad(Bad &b) { return b.x + b.m + b.ok; }
unsigned rd_union(U &u) { return u.lo; }
