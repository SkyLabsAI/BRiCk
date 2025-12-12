/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

class Con {
    char bar[33][20];

    Con() : bar()
    {}
};

class Con2 {
    char foo[42];

    Con2(Con2&& that) = default;
    Con2(const Con2& that) = default;
};

// This doesn't cause an `Earrayloop_init` expression to be emitted.
// Instead, it emits an `Eimplicit_init (Tarray (Tchar W8 Signed) 10)` expression.
class Con3 {
    char qux[10];

    Con3() : qux()
    {}
};
