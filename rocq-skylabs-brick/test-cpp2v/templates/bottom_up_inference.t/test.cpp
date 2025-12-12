/*
 * Copyright (c) 2023-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */

/*
Test the bottom-up type inference in our Gallina parser for template
modules (bluerock.lang.cpp.mparser).

Background: Clang may reasonably delay some type inference in
templated code until specialization/instantiation time.
*/

/*
Note: The Gallina portion of this test (./bottom_up_inference.v) hunts
for terms of these forms and compares the (possibly inferred) type of
`e` with `t`.
*/
#define RESOLVED(e, t) ((void)(e), sizeof(t))
#define SKIP(e) ((void)(e), sizeof(e))
#define UNRESOLVED_MEMBER(e) ((void)(e), 0)
#define UNRESOLVED_UNOP(e) ((void)(e), 1)
#define UNRESOLVED_BINOP(e) ((void)(e), 2)
#define UNRESOLVED_NARY(e) ((void)(e), 3)
#define UNRESOLVED_NEW(e) ((void)(e), 4)
#define UNRESOLVED_DELETE(e) ((void)(e), 5)

using ptrdiff_t = long;
enum class Count : int { One, Two };

template<typename T>
void test() {

    // Assignment
    {
        T t;

        UNRESOLVED_BINOP(t = 1);
        UNRESOLVED_BINOP(t += 1);

        struct S {
            int val;
            S& operator=(const T& t) { val = t.getval(); return *this; }
        };
        S s;
        UNRESOLVED_BINOP(s = t);	// TODO: Could be `RESOLVED(s = t, S&)`

        struct C {
            int val;
            C& operator=(int) { val = 1; return *this; }
            C& operator=(float) { val = 2; return *this; }
        };
        C c;
        UNRESOLVED_BINOP(c = t);	// The choice of overload depends on `T`.
    }

    // Subscript
    {
        T t[4];
        T* p = &t;
        T v;
        const T c;

        RESOLVED(t[1], T);
        RESOLVED(1[t], T);
        RESOLVED(p[1], T);
        UNRESOLVED_BINOP(p[t]); // in practice, there does not seem to be any instantiation of this that works.
        UNRESOLVED_BINOP(v[0]);
        UNRESOLVED_BINOP(0[v]);
        UNRESOLVED_BINOP(c[0]);
        UNRESOLVED_BINOP(0[c]);
    }

    // Pre- and post- increment and decrement
    {
      T t;
      T* p = &t;

      RESOLVED(p++, T*);
      RESOLVED(p--, T*);
      RESOLVED(--p, T*);
      RESOLVED(++p, T*);
      UNRESOLVED_UNOP(t++);
      UNRESOLVED_UNOP(t--);
      UNRESOLVED_UNOP(--t);
      UNRESOLVED_UNOP(++t);

      RESOLVED(+p, long long);
      UNRESOLVED_UNOP(+t);
      UNRESOLVED_UNOP(-t);
    }


    // Binary addition
    {
        T t;
        T* p;

        RESOLVED(p + 1, T*);
        RESOLVED(p + Count::One, T*);
        RESOLVED(1 + p, T*);
        RESOLVED(Count::One + p, T*);
        UNRESOLVED_BINOP(t + 1);
        UNRESOLVED_BINOP(t + Count::One);
        UNRESOLVED_BINOP(1 + t);
        RESOLVED(1 + 1, int);

        // With casts
        {
            T v;
            const T c;

            UNRESOLVED_BINOP(static_cast<T&>(v) + 1);
            UNRESOLVED_BINOP(1 + static_cast<T&>(v));
            UNRESOLVED_BINOP(static_cast<T&&>(v) + 1);
            UNRESOLVED_BINOP(1 + static_cast<T&&>(v));

            UNRESOLVED_BINOP(static_cast<const T&>(c) + 1);
            UNRESOLVED_BINOP(1 + static_cast<const T&>(c));
            UNRESOLVED_BINOP(static_cast<const T&&>(c) + 1);
            UNRESOLVED_BINOP(1 + static_cast<const T&&>(c));
        }
    }

    // Binary subtraction
    {
        T t;
        T* p1; T* p2;
        UNRESOLVED_BINOP(t - 1);
        RESOLVED(1 - 1, int);
        RESOLVED(p1 - p2, ptrdiff_t);
    }

    // Other binary arithmetic operators
    {
        T t;
        UNRESOLVED_BINOP(t & 1);
        UNRESOLVED_BINOP(1 & t);
        RESOLVED(1 & 1, int);
    }

    // Binary relational operators
    {
        T t, t1, t2;
        UNRESOLVED_BINOP(t <= 1);
        UNRESOLVED_BINOP(1 <= t);
        UNRESOLVED_BINOP(t1 <= t2);
        UNRESOLVED_BINOP(t1 <= t2);
    }

}
