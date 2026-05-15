/*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
struct S {
  int x;
  int y;
};

void test() {
  S s;
  s = S();
  S y;
  s = y;
}
