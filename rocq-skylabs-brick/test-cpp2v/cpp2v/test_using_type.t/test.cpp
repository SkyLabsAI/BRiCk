using Foo = int;
using Bar = Foo;

void test(Foo ff) {
  Foo f{0};
  Bar b = f;
}
