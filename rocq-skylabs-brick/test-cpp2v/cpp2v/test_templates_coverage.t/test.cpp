/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

struct P {
    int x;
    void foo();
    virtual void bar();
};

void test() {
    auto field = &P::x;
    auto method = &P::foo;
    auto vmethod = &P::bar;

    P x;
    P* p = &x;
    static_cast<void>(x.*field);
    static_cast<void>(p->*field);
    x.foo();
    p->foo();
    (x.*method)();
    (p->*method)();
    x.bar();
    p->bar();
    (x.*vmethod)();
    (p->*vmethod)();

}
