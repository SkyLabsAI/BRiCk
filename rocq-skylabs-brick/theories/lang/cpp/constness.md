# Why BRiCk Tracks C++ Constness

C++ compiler warnings cannot replace semantic tracking of whether an object was
originally declared `const`. An explicit `const_cast` is well-formed even when a
later write through the resulting reference has undefined behavior.

## A warning-free undefined program

```cpp
#include <cstdio>

int main()
{
    const int x = 1;
    int *p = const_cast<int *>(&x);
    *p = 2; // Undefined behavior: x was originally declared const.

    std::printf("x = %d, *p = %d\n", x, *p);
}
```

Clang 18 accepts this program without a diagnostic, even with all of its
warnings enabled:

```console
$ clang++ -std=c++20 -O2 -Weverything const-ub.cpp -o const-ub
$ ./const-ub
x = 1, *p = 2
```

The optimizer may treat the direct read of `x` as the constant `1`, because a
well-defined execution cannot modify `x`. The read through `p` observes the
value written to memory. Once the program executes undefined behavior, C++ does
not require these observations to agree and does not require the compiler to
issue a diagnostic.

## Why warning on `const_cast` is not a solution

Removing `const` through `const_cast` is not always undefined. It is valid when
the underlying object is not itself const:

```cpp
void set_to_two(int const &x)
{
    const_cast<int &>(x) = 2;
}

int mutable_x = 1;
set_to_two(mutable_x); // Defined: the original object is mutable.

int const immutable_x = 1;
set_to_two(immutable_x); // Undefined behavior.
```

The body of `set_to_two` is identical in both executions. Whether its store is
defined depends on the object supplied by the caller. A compiler processing the
function separately generally cannot determine that provenance. A warning that
rejects every `const_cast` would reject both the defined and undefined calls;
a warning that tries to distinguish them is necessarily incomplete.

Compiler warnings are also optional, compiler-specific diagnostics rather than
part of the C++ execution semantics. A proof that a program has no undefined
behavior therefore cannot assume that warning-free code uses `const_cast`
safely.

## BRiCk's representation of const ownership

BRiCk's `cQp.t` combines a fractional ownership quantity with a bit recording
whether the governed C++ storage is const or mutable. The common notations are:

```coq
1$m (* complete mutable ownership *)
1$c (* complete const ownership *)
```

When C++ constructs a const object, construction first produces mutable
ownership and `wp_make_const` converts it to const ownership:

```coq
Notation wp_make_const tu := (wp_const tu 1$m 1$c).
```

For a class, the conversion follows its C++ object structure. Ordinary fields
and base-class subobjects inherit the containing object's constness. Explicitly
const fields remain const, while `mutable` fields remain mutable. Thus the heap
ownership, rather than only the static type of an expression, records whether a
subsequent store is permitted.

If BRiCk instead discarded a `wp_const` obligation while retaining mutable
ownership, the first example could keep ownership equivalent to `1$m` after
declaring `x` const. The store through `p` could then be proved despite being
undefined in C++.

## Automating the proof obligations

Constness belongs in the semantics, but it should normally not burden client
proofs. A field-owning representation predicate should provide a rule such as:

```coq
Lemma R_const : const.CONST1 module class_name R.
```

This rule states that `wp_const` converts `R`'s const-aware ownership parameter
while preserving its logical model. The `cpp.const` command derives and
registers this rule for ordinary representation predicates after their
equivalence lemma has been derived:

```coq
#[only(equiv)] derive R.
cpp.const R at (class_name) from (module).
```

Once the generated cancellation hint is registered, the standard automation
can discharge routine `wp_make_const` and `wp_make_mutable` obligations. An
opaque representation for an external library cannot be inspected by
`cpp.const`; its const-conversion rule must instead be included explicitly in
that library's trusted specification boundary.

The correct response to noisy const obligations is therefore to supply the
missing representation rule or improve its automation. A rule that simply
deletes `wp_const` is unsound because it loses the distinction demonstrated by
the program above.
