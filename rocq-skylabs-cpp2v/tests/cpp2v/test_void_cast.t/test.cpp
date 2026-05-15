/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

void test(void* p) {
    int* si = static_cast<int*>(p);
    int* ri = reinterpret_cast<int*>(p);
}
