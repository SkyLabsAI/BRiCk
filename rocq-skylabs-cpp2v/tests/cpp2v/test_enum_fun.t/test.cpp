/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

enum A : int {
  X = 0,
  Y = 1,
};

enum class B : unsigned char {
  XX, YY
};

void g(B) { }

void f(A x) {
  g(B::XX);
}

#if 0
int getA() { return X; }
unsigned char ofB() { return XX; }
unsigned int getB_promote() { return XX; }
#endif
B getB() { return B::XX; }

bool compareB() {
  return getB() == B::YY;
}

