/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

struct S {};

int f(int &x) { return x; }
int g(int x) { return x; }

void fS(S &x) { }
void gS(S x) { }
void hS(S *x) { }

int main() {
  int x;
  f(x);
  g(x);

  S s;
  fS(s);
  gS(s);
  hS(&s);

  return 1;
}
