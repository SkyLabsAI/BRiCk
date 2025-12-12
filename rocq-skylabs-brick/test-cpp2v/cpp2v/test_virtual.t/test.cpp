/*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
struct A {
    virtual int f() const = 0;
};

struct B : public A {
    virtual int f() const { return 0; }
};


int call(const A* a) {
    return a->f();
}
