/*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */

/*
Sanity check the value categories of function calls using static
asserts. Some tests assume C++11 or greater.

[1]: https://en.cppreference.com/w/cpp/language/value_category
*/

#include "valcat.hpp"

/*
"a function call [...] whose return type is lvalue refererence" has
value category lvalue [1]
*/
namespace ref_any{
    typedef int t;	// <-- any non-reference type

    t& f();
    struct S{
        t& f();
        t& operator~();
    };
    void test(S& s, t& (*fp)(), t& (S::*mp)()){
        LVALUE (f());	// CallExpr
        LVALUE ((*fp)());	// CallExpr, pointer
        LVALUE (s.f());	// CXXMemberCallExpr
        LVALUE ((s.*mp)());	// CXXMemberCallExpr, pointer
        LVALUE (~s);	// CXXOperatorCallExpr
    }
}

/*
"a function call [...] whose return type is rvalue reference to
function" has value category lvalue (since C++11) [1]
*/
namespace rv_ref_func{
    typedef void(t)();	// <-- any function type

    t&& f();
    struct S{
        t&& f();
        t&& operator~();
    };
    void test(S& s, t&& (*fp)(), t&& (S::*mp)()){
        LVALUE (f());	// CallExpr
        LVALUE ((*fp)());	// CallExpr, pointer
        LVALUE (s.f());	// CXXMemberCallExpr
        LVALUE ((s.*mp)());	// CXXMemberCallExpr, pointer
        LVALUE (~s);	// CXXOperatorCallExpr
    }
}

/*
"a function call [...] whose return type is rvalue reference to
object" has value category xvalue (since C++11) [1] where an "object"
type is any non-functional type (rather than a structure type)
*/
namespace rv_ref_object{
    typedef int t;	// <-- any (non-reference,) non-function type

    t&& f();
    struct S{
        t&& f();
        t&& operator~();
    };
    void test(S& s, t&& (*fp)(), t&& (S::*mp)()){
        XVALUE (f());	// CallExpr
        XVALUE ((*fp)());	// CallExpr, pointer
        XVALUE (s.f());	// CXXMemberCallExpr
        XVALUE ((s.*mp)());	// CXXMemberCallExpr, pointer
        XVALUE (~s);	// CXXOperatorCallExpr
    }
}

/*
"a function call [...] whose return type is non-reference" has value
category prvalue [1]
*/
namespace non_ref{
    typedef int t;	// <-- any non-reference type

    t f();
    struct S{
        t f();
        t operator~();
    };
    void test(S& s, t (*fp)(), t (S::*mp)()){
        PRVALUE (f());	// CallExpr
        PRVALUE ((*fp)());	// CallExpr, pointer
        PRVALUE (s.f());	// CXXMemberCallExpr
        PRVALUE ((s.*mp)());	// CXXMemberCallExpr, pointer
        PRVALUE (~s);	// CXXOperatorCallExpr
    }
}
