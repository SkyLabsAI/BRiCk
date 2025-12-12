(*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(**
   Path notations
 *)
Require Import bluerock.lang.cpp.cpp.

Section with_env.

  Context {σ : genv} `{Σ : cpp_logic}.

  (** ** State Predicates
      [mpred] is the type of predicates that hold on the (system) state.
   *)

  (** ** Representation Predicates
      [Rep] is the type of predicates that hold "at a location".
      Note that [Rep] is essentially [ptr -> mpred].
   *)
  Context (R : Rep).

  (** ** Locations *)

  (** *** Absolute Locations
      these types, i.e. [ptr], [val], [ptr], act like locations *)
  Context (p : ptr) (v : val) (l : ptr).

  (** *** Relative Locations
      these types act like offsets, i.e. relative locations *)
  Context (f : field) (o : offset).


  (** to state that a representation predicates [R] holds at a location [l],
      you use the [|->] operator. *)
  Example _1 : mpred := l |-> R.

  (** because [ptr] and [val] are also "location"-like, representation predicates
      can also hold at them.
   *)
  Example _2 : mpred := p |-> R.
  Example _3 : mpred := _eqv v |-> R.

  (** all of these mean that the location is valid, i.e. it is a valid C/C++
      pointer, but do not (necessarily) imply that the pointer is non-null.
   *)

  (** when the location is a relative location, the predicate itself becomes
      relative, i.e. the type changes from [mpred] to [Rep].
   *)
  Example _4 : Rep := o |-> R.

  (** because [field] is also "offset"-like, they can be used as well. *)
  Example _5 : Rep := _field f |-> R.

  (** note: the value to the right of a [_ |-> _] is *always* a [Rep] regardless
      of whether the left-side is a [ptr] or an [offset]
   *)

  (** locations can be chained together with offsets to produce new locations.
      the following represents the location [l.f]
   *)
  Example _6 : ptr := l ., f.

  (** note that this also works for offsets, but with slightly different syntax: *)
  Example _7 : ptr := l ,, o.

  (** [_ ,, _] can also be used to combine [offset]s into larger [offset]s *)
  Example _8 : offset := o ,, _field f.
  Example _9 : offset := _field f ,, o.

  Example _10 : offset := o ,, _field f ,, _field f. (* is parsed as [(o ,, f) ,, f] *)

  (** using this notation, you can also assert that a [Rep] holds at a compound
      location, e.g. the following means that [R] holds at the location `l.f`.
   *)
  Example _11 : mpred := l ., f |-> R.

  (** note that there is no difference between a compound location and a "basic"
      location, they can be used interchangably
   *)

  (** for uniformity, arbitrary [Rep]s can be positioned, allowing us to write
      predicates such as the following, which is logically equivalent to [_11].
   *)
  Example _11' : mpred := l |-> _field f |-> R.

  (** a benefit to the nested style is that it allows us to factor repeated paths
      out, e.g.
   *)
  Example _12 : mpred :=
    l ., f |-> (_field f |-> R ** o |-> R ** R).

  (** which is logically equivalent to the following *)
  Example _12' : mpred :=
    l ., f ., f |-> R **
    l ., f ,, o |-> R **
    l ., f |-> R.


  (** in addition to fields, we can also use array subscripts *)
  Example _13 : ptr := l .[ Tint ! 5 ]. (* l[[5]] (when [l] is an `int *`) *)
  Example _14 : ptr := l .[ Tuchar ! 5 ]. (* l[[5]] (when [l] is an `unsigned char *`) *)


  (** since these are locations, we can use them to position representation
      predicates *)
  Example _15 : mpred :=
    l .[ Tint ! 5 ] |-> R.

  (** similarly, they can be used with [offset]s and [Rep]s *)
  Example _16 : Rep := .[ Tint ! 3 ] |-> R.
  Example _17 : Rep := o .[ Tint ! -20 ] |-> R.

  (** paths can be chained arbitrarily *)
  Example _20 := l |-> _field f .[ Tint ! 0 ] |-> R.

  Example _21 := l .[ Tint ! 0 ] .[ Tint ! 3 ] |-> R.

  Example _22 := l ., f .[ Tint ! 0 ] ., f |-> R.

  Example _23 := l ., f .[ Tint ! 1 ] .[ Tint ! 0 ] ., f |-> R.

  Example _24 := p ., f .[ Tint ! 1 ] .[ Tint ! 0 ] ., f |-> R.

  Example _25 := o ., f .[ Tint ! 1 ] .[ Tint ! 0 ] ., f |-> R.

  Example _26 := o ., f .[ Tint ! 1 ] .[ Tint ! 0 ] ., f |-> R.

  Example _27 := .[ Tint ! 1 ] |-> R.

  Example _28 := _field f .[ Tint ! 1 ] |-> R.

  Example _29 := p .[ Tint ! 1 ] |-> R.

  Example _30 := _eqv v .[ Tint ! 1 ] |-> R.

End with_env.
