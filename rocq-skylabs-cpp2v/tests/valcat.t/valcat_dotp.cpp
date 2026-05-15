/*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */

#include "valcat.hpp"

struct S{
    int x;
    int m1();
    int& m2();	// <-- rvalue as a member call, prvalue under [.*]
};

// the value category of [.*] varies
void test_dotp(S& s, int S::* field, int (S::*method1)(), int& (S::*method2)()){
    LVALUE(s.*field);
    XVALUE(S().*field);
    /*
    Note: A method pointer must be applied. Its "special prvalue that
    must be applied" value category seems irrelevant.
    */
    PRVALUE((s.*method1)());
    PRVALUE((S().*method1)());
    LVALUE((s.*method2)());
    LVALUE((S().*method2)());

    auto dotp_field_lval = s.*field;
    auto dotp_field_xval = S().*field;
    auto dotp_method_prvalue_1 = (s.*method1)();
    auto dotp_method_prvalue_2 = (S().*method1)();
    auto dotp_method_prvalue_3 = (s.*method2)();
    auto dotp_method_prvalue_4 = (S().*method2)();
}

// the value category of [e1->*e2 := ((*e1)).*e2] follows from the RHS
void test_dotip(S* s, int S::* field, int (S::*method1)(), int& (S::*method2)()){
    LVALUE(s->*field);
    PRVALUE((s->*method1)());
    LVALUE((s->*method2)());
}
