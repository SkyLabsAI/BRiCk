/*
 * Copyright (C) 2023 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

template<typename T, typename U>
struct pair {
  T first;
  U second;

  pair() = default;
  pair(T&& t, U&& u) : first{static_cast<T&&>(t)},
                       second{static_cast<U&&>(u)} {}
  template<typename X> pair(X) {}

  void moop();

  template<typename X> unsigned long test() { return sizeof(X); }
};

template<typename X>
struct pair<X*, X> {
  void moop() { return; }
};

template<typename T, typename U> void pair<T,U>::moop() {}

template<typename T>
void temp(T&) { }

void test() {
  pair<pair<int, int>, char> piic;
}

template<typename T>
class TT {
  TT();
  void foo();
  template<typename U> void tfoo(U);
};
