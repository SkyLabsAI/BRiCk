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

// A pure-virtual re-declaration in the middle of a hierarchy must still
// record its override, so that dispatch on [A*] reaches [D::g].
struct C {
    virtual int g() { return 1; }
};
struct D : C {
    int g() override = 0;
};
struct E : D {
    int g() override { return 3; }
};

int call_g(C* c) {
    return c->g();
}
