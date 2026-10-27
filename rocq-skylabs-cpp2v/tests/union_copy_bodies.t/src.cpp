// A union's defaulted copy/move operations copy its object representation,
// but clang's AST bodies are empty or [return *this;]. cpp2v prints them as
// [Some Defaulted], and the logic copies the active member's bytes.
union U { int a; char b; };

// A [[no_unique_address]] member may extend past the union's data size:
// [T] has size 8 but data size 5, and so does [N]. In [S], [c] sits at
// byte 5, inside [n.t], and [s.n = o.n] copies only 5 bytes. Copying the
// member's [sizeof] would be wrong, so these members get no body.
struct T { T() = default; int a; private: char b; };
union N { [[no_unique_address]] T t; int i; };
struct S { [[no_unique_address]] N n; char c; };

static_assert(sizeof(N) == 8 && __builtin_offsetof(S, c) == 5);

void test(U &u, U &v, S &s, S &o) {
  U w{u};
  U x{static_cast<U &&>(u)};
  u = v;
  u = static_cast<U &&>(v);
  N m{s.n};
  N k{static_cast<N &&>(s.n)};
  s.n = o.n;
  s.n = static_cast<N &&>(o.n);
}
