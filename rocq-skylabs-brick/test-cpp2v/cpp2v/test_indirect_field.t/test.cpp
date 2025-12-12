/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

struct Foo {
    int b;
    struct {
        int x;
    };
    struct {
        int y;
    };

    struct {
        int z;
    } z;

    union {
        struct { int p; };
        struct { char q; };
    };

    Foo():b(0),x(1),p(3) {}
};

int foo(Foo f) {
    return f.b + f.x + f.y + f.z.z + f.p;
}
