/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

class X {
public:
    X() {}
    X(const X&) = default;
    X(X&) = delete;
    ~X();

    typedef int BLAH;

    int get() const {
        if (true && false) { return 0; }
        else { return 1; } }
    int put() const;

    static int fooS();
};

int x;

X::~X() { ::x++; }

int
X::put() const {
    return 1;
}

int
X::fooS() { return 12; }
