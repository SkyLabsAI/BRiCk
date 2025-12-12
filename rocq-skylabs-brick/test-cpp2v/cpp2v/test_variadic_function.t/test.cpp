/*
 * Copyright (c) 2022 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier: MIT-0
 */

int printf(const char *s, ...);

void test() {
    printf("hello");
    printf(", %s", "world");
    printf("%c", '\n');
}
