struct VB { VB(int) {} };

// The implicit copy constructor converts `const D&` to `const VB&`.
struct D : virtual VB { D(int x) : VB(x) {} };
void copy() { D d(1); D e(d); }

// A user-written copy constructor converts the same way.
struct E : virtual VB {
    E(int x) : VB(x) {}
    E(const E &o) : VB(o) {}
};
void copy_explicit() { E d(1); E e(d); }

// A virtual base reached through an intermediate class.
struct M : virtual VB { M(int x) : VB(x) {} };
struct F : M { F(int x) : VB(x), M(x) {} };
void copy_indirect() { F d(1); F e(d); }

// A diamond with a shared virtual base.
struct L : virtual VB { L(int x) : VB(x) {} };
struct R : virtual VB { R(int x) : VB(x) {} };
struct G : L, R { G(int x) : VB(x), L(x), R(x) {} };
void copy_diamond() { G d(1); G e(d); }

// Non-virtual bases.
struct NB { NB(int) {} };
struct N : NB { N(int x) : NB(x) {} };
struct P : N { P(int x) : N(x) {} };
void copy_nonvirtual() { P d(1); P e(d); NB &b = e; P &p = static_cast<P &>(b); }

// A non-virtual base of a class that also has a virtual base.
struct X : virtual VB, NB { X(int x) : VB(x), NB(x) {} };
void convert_mixed(X &x) { NB &b = x; X &y = static_cast<X &>(b); }
