// Local declarations without runtime effect are left out of the [Sdecl]:
// this function stays supported.
namespace N { int v; }
enum class E { a };
int local_decls() {
  typedef int T;
  using U = int;
  struct S { int x; int get() const { return x; } };
  enum F { f0 };
  static_assert(sizeof(T) == 4, "");
  using N::v;
  using namespace N;
  namespace M = N;
  int proto(int);
  extern int ext;
  using enum E;
  U u = 1;
  S s{u};
  return s.get();
}
