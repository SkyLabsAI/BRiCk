/*
 * Copyright (C) 2021 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

void foo(const int) {}
void bar(volatile int) {}

class A {
public:
  void baz(const int) const {}
  virtual void qux(const int) const;
};

void test() {
  foo(1);
  bar(1);

  A a;
  a.baz(1);
  a.qux(1);
}
