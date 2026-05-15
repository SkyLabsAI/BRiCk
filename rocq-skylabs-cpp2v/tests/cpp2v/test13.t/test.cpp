/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

enum X { Y , Z };

enum A : int { B , C };


typedef X TD;
typedef A TE;

void foo() {
  A a = B;
  X x = Y;
  TD z = Z;
}
