/*
 * Copyright (C) 2024 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

template<typename T>
int type_size() { return sizeof(T); }

template<typename T>
struct Box {
  T value;
  Box() : value{} {}
};

struct C {};

void test() {
  Box<int> box_int;
  Box<C> box_C;
  Box<Box<int> > box_box_int;

  type_size<Box<int> >();
  type_size<Box<char> >();
  type_size<Box<C> >();
  type_size<Box<Box<C> > >();

}
