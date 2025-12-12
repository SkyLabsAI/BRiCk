/*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */

#include "valcat.hpp"

namespace member{

    int global;

    struct S {
        int x;
        int& r;
    };

    void lvalues(S s, S& r, S&& x){
        LVALUE(s.x);
        LVALUE(r.x);
        LVALUE(x.x);

        LVALUE(s.r);
        LVALUE(r.r);
        LVALUE(x.r);
        LVALUE((S{1,global}).r);
    }

    void xvalues(){
        struct T { int x; };

        XVALUE(T().x);
    }

}
