/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

int f(int i)
{
    switch (i) {
    case 1:
        [[fallthrough]];
        case 2 : return 1;
    }
    return -1;
}
