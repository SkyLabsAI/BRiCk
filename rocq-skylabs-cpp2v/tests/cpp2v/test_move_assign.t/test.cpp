/*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#if 0
struct V { };

struct XX : public virtual V {
  int x;
};

#endif 
struct YY /* : public XX, virtual V */ {
  union { int a; char b[10]; } x;
  int buf[100];
};

void test() {
  YY y;

}
