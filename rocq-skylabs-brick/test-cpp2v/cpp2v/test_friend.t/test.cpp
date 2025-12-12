/*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
class X {
  friend int get(X&x) {
    return x.x;
  }
  friend int blab(X&);
  friend int blab2(X&);
  int x;
};

int blab(X& x) { return x.x; }
int test() {
  X x;
  return blab2(x);
}
