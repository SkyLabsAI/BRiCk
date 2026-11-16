(*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** this file describes the assumptions made about the compiler.

    in particular, it describes the connection between the semantics
    of C++ declarations (e.g. functions, methods, constructors, destructors),
    and the machine-level specification of the bytes in memory ([wp_fptr]).

 *)

Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.logic.
Require Import skylabs.lang.cpp.semantics.

Section with_Σ.
  Context `{Σ : cpp_logic}.
  Context {ti : thread_info} {σ : genv} (tu : translation_unit).

  (* BEGIN COMPILE SNIPPET *)
  (** compilation of a function [f] is correct if the weakest pre-condition
      of the function ([wp_func]) implies the weakest pre-condition of the
      compiled code ([wp_fptr]).

      The code at [p] was compiled against the program described by [σ], so
      these axioms only hold for translation units [tu] that agree with it
      ([tu ⊧ σ]). Without this premise, a [tu] whose type table disagrees
      with [σ] (e.g. naming a different destructor for a class) would make
      [wp_func tu f] describe code other than what runs at [p].
   *)
  Axiom code_at_ok : tu ⊧ σ -> forall (f : Func) p,
      code_at f p
      |-- Forall ls Q, wp_func tu f ls Q -*
                       wp_fptr (Σ:=Σ) tu.(types) (type_of_value (Ofunction f)) p ls Q.

  Axiom method_at_ok : tu ⊧ σ -> forall (m : Method) p,
      method_at m p
      |-- Forall ls Q, wp_method tu m ls Q -*
                       wp_fptr (Σ:=Σ) tu.(types) (type_of_value (Omethod m)) p ls Q.

  Axiom ctor_at_ok : tu ⊧ σ -> forall (c : Ctor) p,
      ctor_at c p
      |-- Forall ls Q, wp_ctor tu c ls Q -*
                       wp_fptr tu.(types) (type_of_value (Oconstructor c)) p ls Q.

  Axiom dtor_at_ok : tu ⊧ σ -> forall (d : Dtor) p,
      dtor_at d p
      |-- Forall ls Q, wp_dtor tu d ls Q -*
                       wp_fptr tu.(types) (type_of_value (Odestructor d)) p ls Q.
  (* END COMPILE SNIPPET *)

End with_Σ.
