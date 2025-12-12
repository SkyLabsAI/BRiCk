/*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */

#include "valcat.hpp"

struct T { int x[5]; };

void lvalues(int a[3], int* p, T& t){
    LVALUE(a[1]);
    LVALUE(1[a]);
    LVALUE(p[1]);
    LVALUE(1[p]);
    LVALUE(t.x[1]);
    LVALUE(1[t.x]);
}

void xvalues(){

    XVALUE(T().x);
    XVALUE(T().x[2]);

    auto my_subscript = T().x[2];
}
