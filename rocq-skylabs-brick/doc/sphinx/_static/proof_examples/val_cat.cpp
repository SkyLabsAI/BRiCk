/*
 * Copyright (C) 2019 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:MIT-0
 */

struct P {
    int x;

    /**
     * \internal
     *
     * \post _at (_eq this) (PR 0)
     */
    P():x(0) {}
    /**
     * \internal
     *
     * \arg{x} "x" (Vint x)
     * \post this |-> PR x
     */
    P(int x):x(x) {}

    /**
     * \internal
     *
     * \arg{p} "p" (Vptr p)
     * \prepost{m} p |-> PR m
     * \post this |-> PR m
     */
    P(const P&p):x(p.x) {}

    /**
     * Note, this specification is the same as the copy-constructor which is a stronger specification
     * than what is required for more-cosntructors.
     *
     * \internal
     *
     * \arg{p} "p" (Vptr p)
     * \prepost{m} p |-> PR m
     * \post this |-> PR m
     */
    P(const P&& p):x(p.x) {}

    /**
     * \internal
     *
     * \pre{m} this |-> PR m
     * \post emp
     */
    ~P() {}
};

struct Q {
    int x;
    explicit Q() {}
};

/**
 * \internal
 *
 * \arg{x} "x" (Vptr x)
 * \prepost{m} x |-> PR m
 * \post[Vint m] emp
 */
int by_ref(P& x) { return x.x; }

/**
 * \internal
 *
 * \arg{x} "x" (Vptr x)
 * \prepost{m} x |-> PR m
 * \post[Vint m] emp
 */
int by_val(P x) { return x.x; }

/**
 * \internal
 *
 * \arg{x} "x" (Vptr x)
 * \prepost{m} x |-> PR m
 * \post[Vint m] emp
 */
int by_ptr(P *x) { return x->x; }

/**
 * \internal
 *
 * \arg{x} "x" (Vptr x)
 * \prepost{m} x |-> PR m
 * \post[Vint m] emp
 */
int by_rref(P &&x) { return x.x; }

/**
 * \internal
 *
 * \post{p}[Vptr p] p |-> PR 1
 */
P ret_val() {
    return P(1);
}

/**
 * \internal
 *
 * \arg{x} "x" (Vptr x)
 * \prepost{m} x |-> PR m
 * \post{p}[Vptr x] emp
 */
P& ret_ref(P& x) {
    return x;
}

/**
 * \internal
 *
 * \arg{x} "x" (Vptr x)
 * \prepost{m} x |-> PR m
 * \post{p}[Vptr x] emp
 */
P&& ret_rref(P& x) {
    return static_cast<P&&>(x);
}

/**
 * \arg{a} "a" (Vbool a)
 * \require a = true
 * \post emp
 */
extern void assert(int a);

/**
 * \post[Vint 0] emp
 */
int main() {
    P p;

    by_ref(p);

    by_val(p);

    by_ptr(&p);

    by_val(P());

    by_val(P(P().x));

    by_val(P(ret_val().x));

    by_rref(P());

    (void)(P().x);

    by_ref(ret_ref(p));

    by_val(ret_rref(p));

    by_val(ret_val());

    ret_val();

    P pp(ret_rref(p));

    return 0;
}
