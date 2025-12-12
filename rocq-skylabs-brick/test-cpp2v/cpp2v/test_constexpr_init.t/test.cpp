/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

constexpr int FOO = 0;
constexpr int BAR = ~0;
template<typename T>
class C {
    static constexpr long long BAZ = 0x0ull;
    static constexpr long long BAB = ~0x0ull;
};


template class C<int>;
