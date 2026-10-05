(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** [--elaborate] must skip template patterns but still elaborate
    specializations.  Each [pattern_*] program used to crash cpp2v; libstdc++'s
    <<ostream>> has the shape of [pattern_decl]. *)

Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.

Definition get (tu : translation_unit) (n : name) :=
  (n , tu.(symbols) !! n).

(** * Templated classes reached outside a class template's body *)

(* An explicit instantiation declaration. *)
#[duplicates(error), elaborate]
cpp.prog pattern_decl prog cpp:{{
  namespace n {
    template <class T> struct O { class S; };
    template <class T> class O<T>::S { };
  }
  namespace n {
    extern template class O<char>;
  }
}}.

(* An explicit instantiation definition, which also instantiates the members'
   definitions. *)
#[duplicates(error), elaborate]
cpp.prog pattern_defn prog cpp:{{
  namespace n {
    template <class T> struct O { class S; void f() {} };
    template <class T> class O<T>::S { public: S() {} };
  }
  namespace n {
    template class O<char>;
  }
}}.

(* A partial specialization, and a member class of it. *)
#[duplicates(error), elaborate]
cpp.prog pattern_partial prog cpp:{{
  namespace n {
    template <class T> struct P;
    template <class T> struct P<T*> { struct S; };
    template <class T> struct P<T*>::S { T *p; };
  }
  namespace n {
    template struct P<int*>;
  }
  n::P<int*>::S s;
}}.

(** * Specializations are still elaborated *)

#[duplicates(error), elaborate]
cpp.prog spec_elab prog cpp:{{
  namespace n {
    template <class T> struct O { struct S; S *s; };
    template <class T> struct O<T>::S {
      S() = default;
      S(const S&) = default;
      S& operator=(const S&) = default;
      T t;
    };
  }
  namespace n {
    template struct O<int>;
  }
}}.

#[duplicates(error)]
cpp.prog spec_plain prog cpp:{{
  namespace n {
    template <class T> struct O { struct S; S *s; };
    template <class T> struct O<T>::S {
      S() = default;
      S(const S&) = default;
      S& operator=(const S&) = default;
      T t;
    };
  }
  namespace n {
    template struct O<int>;
  }
}}.

Eval vm_compute in get spec_elab "n::O<int>::S::S(const n::O<int>::S&)".
Eval vm_compute in get spec_plain "n::O<int>::S::S(const n::O<int>::S&)".
Eval vm_compute in get spec_elab "n::O<int>::S::operator=(const n::O<int>::S&)".
Eval vm_compute in get spec_plain "n::O<int>::S::operator=(const n::O<int>::S&)".
