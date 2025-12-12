class A {};
class B : public A {};
class C : public B {};
class D : public C {};

void test() {
  D* d;
  A& a = *d;
  A&& l = static_cast<A&&>(*d);
  static_cast<A*>(d);
  B* bb = nullptr;
  A* aa = static_cast<A*>(nullptr);
  A* aaa = static_cast<A*>(bb);
}
