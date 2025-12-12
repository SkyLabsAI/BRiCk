struct A {
  virtual void foo() = 0;
};


struct B : public A {
};
struct C : public B {
  virtual void foo() { }
};
struct D : public C {
  virtual void foo() { }
};
