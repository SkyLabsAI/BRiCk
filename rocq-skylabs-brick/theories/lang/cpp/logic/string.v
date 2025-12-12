(*
 * Copyright (C) 2019-2021 BlueRock Security, Inc.

 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export bluerock.lang.cpp.logic.core_string.
Require Export bluerock.lang.cpp.logic.cstring.
Require Export bluerock.lang.cpp.logic.zstring.

(** * [cstring]s and [zstring]s

    In C++, strings are backed by character arrays; it is easiest to bootstrap our
    string theory by using *null-terminated* [list Z]s as the Coq model type - which
    is what the [zstring] module does. Atop these [zstring]s we can derive the
    concept of [cstring]s which re-express the same [zstring] representation predicates,
    utilities and theory in terms of a [BS.t] (bytestring) Coq model carrier type. You
    should *almost always* use a [cstring] concept instead of a [zstring] concept
    if possible, as the automation has been tuned to work best for the former; there are
    sufficient reasoning principles for converting between the two if necessary.
 *)
(** ** Notes
    - We omit discussion of [zstring]s from here on out due to their aforementioned
      subsumption by [cstring]s.
    - Whereas [cstring.t := BS.t] *does not* contain a null-terminator,
      [zstring.t := list Z] *does* contain a null-terminator; the conversion
      utilities deal with appropriately inserting/stripping this null-terminator.
    - The `'` variant of the [WF] predicate uses an alternative formulation which
      was more useful during a previous iteration of some downstream proofs.
      We retain this alternative formulation so that we can avoid re-proving that
      code, but you should *always* prefer to use [WF] over [WF']. However, there
      are sufficient reasoning principles for seamlessly switching between the two.
    - Due to scope complexities, some definitions are actually notations which
      wrap an identically-named term which is prefixed by an underscore; use this
      underscore-prefixed version if Coq complains about a notation not being
      fully applied.
 *)
(** * [cstring.t] and [cstring.WF] - Well Formed [BS.t]s (bytestrings) as a Carrier Type for C++ Strings

    While it is useful to take advantage of Coq's bytestrings to model C++ strings,
    this is not quite strong enough. In particular, C++ strings are null-terminated
    and thus cannot contain any intervening zeros. While we could've bundled
    this well-formedness side-condition into the carrier type, we decide instead
    to separate it out into a predicate [cstring.WF : cstring.t -> Prop]. This has
    the added benefit of easing the proof of the core [cstring.t] theory since we
    avoid the use of dependent records.

    The following is a rough enumeration of the definitions and theory related to
    [cstring.t] and [cstring.WF]:
    - [cstring.t := BS.t]: bytestrings as a carrier type for C++ strings
    - [cstring.WF (cstr : cstring.t) : Prop := <cstr doesn't contain the zero-byte>]:
      well-formedness of [cstring.t]s.
    - [cstring.size (cstr : cstring.t) : Z
         := <length of the string *including* the null-terminator>]
    - [cstring.strlen (cstr : cstring.t) : Z
         := <length of the string *excluding* the null-terminator>]
      - This function mirrors the behavior of `std::strlen` in C++
    - [cstring.from_zstring]/[cstring.to_zstring]: utilities for converting back and
      forth between [cstring.t]s and [zstring.t]s while appropriately inserting/
      stripping the null-terminator to accomodate the fact that we exlude it for
      [cstring]s.
 *)
(** * [cstring.R] - Fixed Sized Strings

    Very often we are interested in dealing with a string as a fixed(-size) value,
    and [cstring.R (q : Qp) (cstr : cstring.t) : Rep] reflects [q]-ownership of the
    null-terminated character-array which contains the *non-null-terminated* and
    [cstring.WF] bytestring [cstr]. This rep is useful for dealing with string constants
    that are inserted by the compiler and passed around/read during execution;
    while it would be reasonably straightforward to add theory for modifying characters
    in a random-access way, the [BS.t] theory for this is somewhat lacking and so
    the use-case languishes for now.
 *)
(** * [cstring.bufR] - Dynamic Sized Strings Backed by Fixed Sized Character Arrays

    String constants read into a fixed-sized buffer present a slightly different use
    case. If the buffer has size [sz], it contains some [cstring.t] [cstr] which is
    [cstring.WF], and [cstring.size cstr <= sz] then the "weakest" valid representation
    is:

       ```
       cstring.R q cstr **
       Exists l,
         .[Tuchar ! cstring.size cstr] |-> arrayR Tuchar (fun _ => anyR q Tuchar) l **
         [| cstring.size cstr + length l = sz |]
       ```

    However, we want to be able to easily add new characters to our buffer and -
    ideally - remove them in a disciplined way. Given that our existing definitions
    require our string to be null-terminated in memory, it is not obvious how we would
    justify such `push_back`/`pop_back` reasoning principles while avoiding an explicit
    binding and characterization of the tail of the buffer. To address this we we
    restrict our definition of [cstring.bufR q sz cstr] to use [primR Tuchar q 0]
    instead of [anyR q Tuchar].

    With this approach, a [cstring.bufR q sz cstr] fact allows you to `push_back` a new
    character to the [cstring.t] model by writing it to the [cstring.bufR]
    at position [.[Tuchar ! cstring.size cstr]]. Furthermore, the tail of the
    [cstring.t] model can be removed by zeroing that portion of the [cstring.bufR].

    Note: at the moment the theory supporting this `push_back`/`pop_back` use-case
    is not fully fleshed out, but ongoing verification efforts will allow us
    to backfill the needed things.
 *)
