// A delegating initializer with non-dependent arguments in a member template.
struct S {
  S(int) {}

  template<typename T>
  S(T) : S(0) {}
};

// Delegation outside any template.
struct A {
  A(int) {}
  A() : A(0) {}
};

// Base initializers keep their written base type, alias included.
struct B { B(int) {} };
using Alias = B;
struct D : Alias {
  D(int x) : Alias(x) {}

  template<typename T>
  D(T) : D(0) {}
};

// Delegation in a class template.
template<typename T>
struct C {
  C(int) {}
  C() : C(0) {}
};

// A dependent base, then delegation.
template<typename T>
struct E : T {
  E(int x) : T(x) {}
  E() : E(0) {}
};

// Pack-expanded base initializers.
template<typename... Bs>
struct P : Bs... {
  P() : Bs(0)... {}
};

void use() {
  S s(1.0);
  D d(1.0);
  C<int> c;
  E<B> e;
  P<B> p;
}
