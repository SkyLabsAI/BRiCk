/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */
enum X {
  AA , A = 1 + 1, B = 1 << 8 , CC
};

enum class C;
enum class C {
  L = 1 + 1, R = 1 << 7
};

enum : unsigned short {
  GLOBAL = 3
};

enum {
  GLOBAL2 = 2
};

namespace {
  enum { GLOBAL3 = 3 };
};

void test() {
  (void) AA;
  (void) X::AA;
  (void) C::L;
  (void) GLOBAL;
  (void) GLOBAL2;
  (void) GLOBAL3;
}
