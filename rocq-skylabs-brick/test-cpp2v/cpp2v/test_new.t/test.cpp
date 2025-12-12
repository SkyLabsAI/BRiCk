/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */
//#include <stdio.h>

struct C {
  ~C() { /* printf("1"); */ }
};

int main() {
  auto p = new C[5][6];
  delete[] &(p[0][0]);
}
