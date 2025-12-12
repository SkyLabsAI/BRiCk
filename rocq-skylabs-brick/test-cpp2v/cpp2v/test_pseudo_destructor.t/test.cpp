/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

template<typename T>
void destroy(T* ptr) {
  ptr->T::~T();
}

template void destroy<int>(int*);
