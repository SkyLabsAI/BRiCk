# Writing Specifications

Specifications are represented as pre- and post-conditions. They can be written using notation that makes them reminiscent of doxygen comments.

+ `\with (x : T) ... (y : U)` represents universally quantified variables that scope
  over *both* the pre- and the post-condition.
+ `\let x := e` represents a standard `let` expression assigning the value of
  of the *Gallina* expression `e` to the /pattern/ `x`.
+ `\prepost P` adds the separation logic assertion `P` to the pre- *and* the
  post-condition
+ `\arg nm e` adds to the pre-condition that the value of the "current" argument
  should unify with `e`. Currently, `nm` (a string) is used for documentation
  purposes only.
  - This syntax also supports with binders, e.g. `\arg{x} "x" (Vint x)`. Jus
    like `\with`, variables are quantified over both thr pre- and thr post-condition.
    If you want to specify the type of the quantified variable,
    `\arg{(x:Z) (y:nat)} "x" (Vint x)`
+ `\args es` adds `es` arguments to the current list of arguments (note that `es`
  is a list).
+ `\require P` adds the *pure* (i.e. of type `Prop`) fact `P` to the pre-condition
+ `\pre P` adds the spatial (i.e. of type `mpred`) fact `P` to the pre-condition
+ `\post{x .. y}[r] Q` represents a post-condition of `Q`. The variables `x` .. `y` are binders (like in `\with`)
  but scope only over the post-condition. The expression `r` will unify with the
  return value.
+ `\post[r] Q` represents a post-condition of `Q`. The variables `x` .. `y` are binders (like in `\with`)
  but scope only over the post-condition. In this syntax, `r` is a binder of type
  `val`.
+ `\post Q` represents a post-condition of `Q`. The variables `x` .. `y` are binders (like in `\with`)
  but scope only over the post-condition. In this syntax, the return type must
  be `void`.

Note that you can have any number of `\pre`, but `\post` must be the last command, i.e.
you *can not* write `\post P \pre Q`.

### Advanced constructions

+ `\withT ts <- tele` represents binding the values of a telescope universally.
  This is *not* commonly used, but can be useful for higher-order functions.
+ `\exact wpp` includes exactly the pre/post condition `wpp`.

## Simple Examples

A function to return 0. Note it is legal, but not idiomatic, to drop `\pre empSP`.

```coq
\pre empSP
\post{}[Vint 0] empSP
```

A function to return its parameter plus 1 (note the pre-condition is necessary
to ensure that the addition does not overflow).

```coq
\arg{n} "n" (Vint n)
\require has_type_prop (n+1) (Tnum W32 Signed)
\post{}[Vint (n + 1)] empSP
```

A function to read the (integer) value stored at a pointer (note that this
function only requires fractional ownership of the underlying pointer).

```coq
\with (v : Z) (q : Qp)
\arg{p} "p" p
\prepost _at (_eq p) (tint W32 q v)
\pre empSP
\post{}[Vint v] empSP
```

It is idiomatic to place each pure fact in its own `\require` clause and to quantify variables on `\arg` when they are essentially the values, e.g.

```coq
\arg{n} "n" (Vint n)
\arg{m} "m" (Vint m)
\require n < m
\require Even n
\pre empSP
\post{}[Vint n] empSP
```
