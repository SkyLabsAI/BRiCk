/*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */

class B {
public:
  int get0() { return 0; }
};

class X : protected B {
public:
  using B::get0;
};

int test() {
  X x;
  return x.get0();
}
