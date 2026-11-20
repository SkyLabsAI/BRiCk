/*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 *
 * SPDX-License-Identifier: MIT-0
 */

int try_add_one(int x) {
    int y = 0;
    try {
        y = x + 1;
    } catch (...) {
        y = -1;
    }
    return y;
}
