/*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
struct X {
  int foo() const { return 1; }
  int bar() { return 0; }
  X make() { return X(); }

  virtual int baz() const { return 0; }
};

struct Y : X {
  virtual int baz() const { return 1; }
};

int main() {
  X x;
  x.foo();
  x.bar();
  x.make().bar();

  auto f = &X::foo;

  (x.*f)();

  auto ff = &X::baz;

  Y y;
  return (x.*ff)() + (y.*ff)();
}
