/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

int test() {
    int x = 0;
    switch(1) {
    case 0:
        ++x;
    case 1:
    case 2:
        return 1;
    case 3 ... 4:
        x++;
    case 5:
        return x;
    case 6:
        if (x == 0) break;
    case 7:
        return 11;
    default:
        break;
    }
    return 0;
}
