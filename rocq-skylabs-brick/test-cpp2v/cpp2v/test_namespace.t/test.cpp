/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

namespace things { int x; }

int test() {
    using namespace things;
    return x;
}
