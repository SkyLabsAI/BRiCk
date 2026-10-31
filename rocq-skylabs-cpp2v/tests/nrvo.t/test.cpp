// Returns eligible for named return value optimization
// ([class.copy.elision]/1.1) print as [Sreturn_nrvo x e]: the copy or move
// [e] from the automatic variable [x] may be elided, so BRiCk verifies both
// executions. The eligibility is the standard's, not clang's decision: clang
// marks neither return of [two] as a candidate, but a conforming
// implementation may still elide one of them.
struct S {
  int *c;
  S(int *p) : c(p) {}
  S(const S &o) : c(o.c) { ++*o.c; }
  S(S &&o) : c(o.c) { ++*o.c; }
  ~S() {}
};

// Clang's NRVO candidate.
S make(int *p) {
  S x(p);
  return x;
}

// Two candidates: clang elides neither, the standard permits either.
S two(int *p, bool b) {
  S x(p);
  S y(p);
  if (b)
    return x;
  return y;
}

// The inner [x] is returned; the outer one is destroyed normally.
S shadow(int *p) {
  S x(p);
  {
    S x(p);
    return x;
  }
}

// A [const] local has the same type ignoring cv-qualification.
S const_local(int *p) {
  const S x(p);
  return x;
}

// Not eligible: a parameter.
S param(S s) {
  return s;
}

// Not eligible: a static local, and a variable of an enclosing function
// (lambda capture).
S not_automatic(int *p) {
  static S s(p);
  S x(p);
  auto f = [&]() -> S { return x; };
  f();
  return s;
}

// Not eligible: a different type (a derived object is sliced).
struct T : S {
  T(int *p) : S(p) {}
};
S sliced(int *p) {
  T t(p);
  return t;
}

// Not eligible: volatile.
S volatile_local(int *p) {
  volatile S x(p);
  return S(p);
}

// Not a constructor call at all: C++17 guaranteed elision of a prvalue.
S prvalue(int *p) {
  return S(p);
}

// The expression [e] for different constructors of the returned class.

// Only a constructor from a const rvalue reference.
struct CR {
  CR();
  CR(const CR &&);
  CR(const CR &) = delete;
};
CR const_rvalue_ref() {
  CR x;
  return x;
}

// Copy-only: a user-declared copy constructor suppresses the implicit move,
// so the copy constructor binds the implicitly moved [x].
struct Cp {
  Cp();
  Cp(const Cp &);
};
Cp copy_only() {
  Cp x;
  return x;
}

// A defaulted move constructor.
struct Df {
  Df();
  Df(Df &&) = default;
  ~Df();
};
Df defaulted_move() {
  Df x;
  return x;
}

// Implicit, trivial copy and move constructors.
struct Tr {
  int a;
};
Tr trivial() {
  Tr x{1};
  return x;
}

// A class template instance.
template <typename X> struct W {
  X v;
  W();
  W(W &&);
};
W<int> templ() {
  W<int> x;
  return x;
}
