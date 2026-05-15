/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

void test() {
    enum X { A , B };
    struct Y { int x; X tg; };

    X a;
    Y b;

    b.x++;
    a = B;
}
