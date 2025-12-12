Require Import bluerock.lang.cpp.syntax.

(** Heap types (aka 'runtime types') are the subset of types
    that are known at runtime.

    Because <<const>>ness and <<volatile>>ness are reflected
    using separation logic principles, qualifiers are not preserved
    in runtime types.

    Additionally, types such as [Tincomplete_array] are not runtime
    types, they are static approximations of the single runtime type
    of arrays, i.e. [Tarray].
 *)
Notation Rtype := type (only parsing).

Fixpoint is_Rtype (s : type) : bool :=
  match s with
  | Tnum _ _
  | Tvoid
  | Tbool
  | Tnullptr
  | Tchar_ _
  | Tfloat_ _ => true
  | Tptr t | Tref t | Trv_ref t => is_Rtype t
  | Tincomplete_array _
  | Tvariable_array _ _ => false
  | Tarray t _ => is_Rtype t
  | Tfunction _ => true (* more neuanced? *)
  | Tnamed _ | Tenum _ => true
  | _ => false (* TODO *)
  end.
