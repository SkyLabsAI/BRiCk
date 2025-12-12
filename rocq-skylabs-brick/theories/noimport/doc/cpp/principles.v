(*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** * Principles

Some principles for sanity checking specifications

Principles
Rule 0. If you can find a way to "break" separation logic using your function,
        your specification is wrong.
Rule 1. If there is more ownership in the post-condition, the function "must"
        allocate
Rule 2. If there is more ownership in the pre-condition, the function "must"
        free resources
Rule 3. If there is a logical variable that is not related to a program value,
        something is probably wrong, e.g. a memory leak or doing extra work
Rule 4. The term to the left of a |-> must *always* evaluate to a pointer.
        (if this isn't true, the points to fact is the same as "False")
Rule 5. The pre-condition must be satisfiable.
        (there is *some* heap that the assertion holds on)
Rule 6. If the post-condition is not satisfiable, the function can not return.
Rule 7. Any function marked "noreturn" should have a post-condition of
        `[| False |]` (or `lfalse`)
Rule 8. All variables must be "declared" / "quantified"
"Rule". The right hand side of |-> is always a "Rep" (usually ending in R, e.g.
        intR, llistR, ...)
Rule 9. if the type of the parameter is a pointer, an array, a reference,
        an rvalue_reference, or a struct/union, then the second parameter to
        \arg is *ALWAYS* a ptr.
Rule 10. If you do not need to modify a value, then you should require only a
         fraction of it.
  Addendum: avoid coupling fractions unless it is necessary
Rule 11. If a value changes from the precondition to the post-condition you
         will need full ownership of it.
Rule 12. Parameters that are strictly output parameters should occur in the
         pre-condition with anyR “typename” 1
Rule 13. (concurrency) Representation predicates should be "stable" with
         respect to other threads.

Syntax:
"Rule". If an assertion is inside of "[| |]", then it has *no* resources
        (it could hold in an empty program)

*)
