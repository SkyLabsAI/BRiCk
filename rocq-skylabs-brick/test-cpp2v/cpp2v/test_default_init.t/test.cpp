/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

struct Foo {
  int a { 1 };
  int b = 2;

  Foo() {}
  Foo(int x) : b(x) {}
};
