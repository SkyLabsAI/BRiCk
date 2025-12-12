/*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */

#include "valcat.hpp"

struct S{ int a[3]; };
void test() {
    /*
    Interestingly, clang emits an ArrayToPointerCast making the array
    part of the subscript expression have type `int*` and yet it
    correctly assigns value category `xvalue` to the subscript as a
    whole.
    */
    //int&& subscript_xvalue = S().a[0];
    XVALUE(S().a[0]);
}
