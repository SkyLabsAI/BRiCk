/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

class X {
public:
  X() {}

  static X make() { return X(); }
  static X make2();
  static X make3() { static int c = 0; return X(); }
};


int count() {
  static int value = 0;
  return value++;
}
