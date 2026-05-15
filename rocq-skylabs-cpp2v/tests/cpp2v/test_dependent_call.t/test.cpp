/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

template <typename T>
class X
{
  int lookup();
};

template <typename T>
int X<T>::lookup()
{
  return T::f();
}

struct Y {
    static int f() { return 0; }
};

template class X<Y>;
