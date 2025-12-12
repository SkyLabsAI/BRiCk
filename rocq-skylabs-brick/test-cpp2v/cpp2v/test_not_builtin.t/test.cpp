/*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */

extern "C" {
unsigned long strlen(const char *msg) {
    unsigned result = 0;
    while (*msg) {
        result++;
        msg++;
    }
    return result;
}
}

unsigned test() {
    return strlen("100");
}
