/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

struct Foo {
    Foo() {};
    Foo(int):Foo() {}
};
