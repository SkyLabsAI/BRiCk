/*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
// #include <stdint.h>

using uint32_t = unsigned int;

uint32_t bswap(uint32_t x) {
    return __builtin_bswap32(x);
}
