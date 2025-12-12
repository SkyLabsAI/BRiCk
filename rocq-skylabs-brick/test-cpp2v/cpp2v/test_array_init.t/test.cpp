/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

struct P {
    int x;
    int y { 7 };
};

struct PP {
    P a, b;
};

void test() {
    int x[3] = {0};
    int y[2] = {1,2};
    int z[2][2] = { { 1 , 2 } , { [1] = 4 } };
    int a[10] = { [9] = 1 };
    int b[10] = { 1 };
    P p = { .x = 1 , .y = 2 };
    P ps[2] = { };
    PP pp = { 1 , 2 };
}
