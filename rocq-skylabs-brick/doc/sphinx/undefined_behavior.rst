.. _undefined_behavior:

#############################################################
Undefined behavior and optimizations
#############################################################

C++ programmers want compilers to produce fast code without exploiting undefined
behavior. But that is impossible, so (optimizing) compilers opt to produce fast
code instead. Hence, to formally verify C++ programs are correct, we must prevent
programs from having UB.

This page motivates informally the need for some UB, by showing that exploiting
UB is necessary even for obvious optimizations. You are welcome to skip this
page, but it will give intuition for other content in this guide.

We assume you are familiar with programming in C++.

A minimal example
=================

We show undefined behavior on an example. For clarity, we pick a small example.
This example might seem artificial, but it shows issues that affect real
programs.

In the snippet below, the function `foo` seems equivalent to
`foo_opt`\ [#provenance-example]_, but the latter can avoid re-reading `x` from
memory, so we expect optimizers to transform the former into the latter.

.. code-block:: cpp

  int foo() {
    long x = 5;
    bar();
    return x;
  }

  int foo_opt() {
    bar();
    return 5;
  }

Indeed, whatever `bar()` does, this optimization preserves program behavior, as
defined by the C++ standard, and compilers indeed perform it.

However, that optimization changes the program behavior if `bar()` looks like
the following strange example:

.. code-block:: cpp

  void bar() {
    long y = 0;
    long* px = &y + 5; // "5" is platform-specific
    *px = 4;
  }

On our test platform\ [#godbolt-example]_, `px` will contain the address of `x`,
so without optimizations `foo()` will return `4`; but with the optimization
above, `foo()` returns `5`.

We claimed our optimization preserves program behavior, yet it appears to change
`foo()`'s return value; how is that possible?
At the same time, this optimization is desirable; and if this small optimization
were illegal, would we have a chance to perform more complex optimizations?

As a solution, the C++ standard ensures that `bar()` contains *undefined
behavior* (UB), and allows programs to implement undefined behavior arbitrarily.
In particular, `bar()` is UB because it takes a pointer to a variable (`y`),
increments it until it has the address of another variable (`x`), then writes
through this pointer.

.. rubric:: Footnotes
.. [#provenance-example] Based on `this example
  <https://web.archive.org/web/20210819142604/https://news.ycombinator.com/item?id=27562962>`_.

.. [#godbolt-example] At least on a specific compiler, according to `Godbolt <https://godbolt.org/z/8cha4Ebfo>`_.
