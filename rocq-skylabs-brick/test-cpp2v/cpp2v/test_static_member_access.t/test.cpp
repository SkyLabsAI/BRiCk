/*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
namespace test1 {
struct C {
  int mem;
  static int sta;
  static int get() { return 0; }
  int gett() { return 0; }
};

void test() {
  C c;
  (void)c.mem;
  (void)c.sta;
  c.get();
  c.gett();
  (void)&C::get;
  (void)&C::gett;
  (void)&test;
}
}

namespace test2 {
  struct C {
    static int foo() { return 0; }
    static int bar() { return 1; }
    int baz() const { return 2; }
  };

  struct D {
    C c;
    static C cc;

    enum {
      X = 0
    };
  };

  void test() {
    const C c;
    c.foo();
    c.bar();
    c.baz();
    const C* p = &c;
    p->foo();
    p->bar();
    p->baz();

    D d;
    (void)d.X;
    d.c.foo();
    d.cc.foo();
  }
}
