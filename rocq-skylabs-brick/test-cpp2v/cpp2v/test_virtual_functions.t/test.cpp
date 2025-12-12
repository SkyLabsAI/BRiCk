/*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
struct A {
    virtual int foo() const = 0;
    int bar() const { return foo(); }
    virtual ~A() = default;
};

struct B : public A {
//    virtual int foo() const { return 1; }
    virtual ~B() = default;
};

struct C : public B {
    C() = default;
    virtual int foo() const { return 2; }
    virtual ~C() = default;
};

int main() {
    C* c = new C();
    B* b = static_cast<C*>(c);
    A* a = static_cast<C*>(a); // somewhat surprisingly, this actually type checks, but it has UB

    c->B::foo(); // "direct" dispatch
    b->foo();    // virtual dispatch (after a cast to <A>)
    a->foo();    // virtual dispatch

    return 0;
}
