/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

int test() {
    const char* foo = __FUNCTION__;
    return __LINE__;
}

// Despite the fact that the string is not an ascii
// string, the __FUNCTION__ macro still produces ascii.
void σϵγΓ𑀅𑀙() { (void)(__FUNCTION__); }
