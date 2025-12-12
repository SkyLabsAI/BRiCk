(*
 * Copyright (C) 2020-2022 BlueRock Security, Inc.
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import stdpp.decidable.
Require Import bluerock.lang.cpp.syntax.
Require Import bluerock.lang.cpp.semantics.genv.
Require Import bluerock.lang.cpp.semantics.subtyping.

(** Dispatching to a virtual function contains two pieces:
    1. Finding the correct function to invoke
    2. Fixing up the dispatch object.
    Consider the following example
    ```c++
    struct A { virtual void foo() = 0; };
    struct B : public A { virtual void foo() { } };

    A* a = new B();
    a->foo(); // same as [static_cast<B*>(a)->B::foo()]
    ```
    NOTE in order to dispatch to the overridden function
         the [dispatch] function also introduces a cast to
         get a pointer of the correct type.
 *)

Section dispatch.
  Context (σ : genv).

  Definition list_get {T} (t : name) (l : list (name * T)) : option T :=
    snd <$> List.find (fun '(t',_) => bool_decide (t = t')) l.

  (** [dispatch path fn = Some (impl_class, impl_path, impl_fn)]
      dispatches [fn] (the name of a member function on [Tnamed base])
      given the path [path] (which is [mdc..base].
      NOTE: [path] takes the form of the [path] argument to [identity].
      NOTE: [base_to_derived impl_class impl_path] is the cast used to
            construct the new `this` pointer.
      - [impl_class] is the name of the class that is providing the implementation
      - [impl_fn] is the name of the function to call
      - [impl_path] is the path from (base..impl].
      Some examples assuming:
      ```c++
      struct A { virtual void f(); };
      struct B : public A { virtual void f(); };
      struct C : public B { };
      ```
      - [dispatch ["::C","::B","::A"] "A::f()" = Some ("::B", ["::A"], "B::f()")]
      - [dispatch ["::C","::A"] "B::f()" = Some ("::B", [], "B::f()")]
   *)
  #[local] Fixpoint dispatch (base : globname) (path : list globname) (fn : obj_name)
    : option (globname * list globname * obj_name) :=
    match path with
    | nil =>
        (* virtual dispatch is not allowed on uninitialized objects *)
        None
    | bottom :: nil =>
        (* to perform virtual dispatch, the identity must be a
           path from [base] to a most-derived-class *)
        if bool_decide (bottom = base)
        then Some (base, [], fn)
        else None
    | next :: rest =>
        dispatch base rest fn ≫= fun rr =>
          match glob_def σ next with
          | Some (Gstruct st) =>
              let '(_, _, override) := rr in
              match list_get override st.(s_overrides) with
              | Some cand' => Some (next, rest, cand')
              | None => Some rr
              end
          | _ => None
          end
    end.

  Section tu.
    Variable tu : translation_unit.

    #[local] Fixpoint tu_dispatch (base : globname) (path : list globname) (fn : obj_name)
      : option (globname * list globname * obj_name) :=
      match path with
      | nil =>
          (* virtual dispatch is not allowed on uninitialized objects *)
          None
      | bottom :: nil =>
          (* to perform virtual dispatch, the identity must be a
           path from [base] to a most-derived-class *)
          if bool_decide (bottom = base)
          then Some (base, [], fn)
          else None
      | next :: rest =>
          tu_dispatch base rest fn ≫= fun rr =>
            match tu.(types) !! next with
            | Some (Gstruct st) =>
                let '(_, _, override) := rr in
                match list_get override st.(s_overrides) with
                | Some cand' => Some (next, rest, cand')
                | None => Some rr
                end
            | _ => None
            end
      end.

    Theorem tu_dispatch_ok (MOD : tu ⊧ σ) : forall path base fn a b c,
        tu_dispatch base path fn = Some (a,b,c) -> dispatch base path fn = Some (a,b,c).
    Proof.
      induction path; simpl; intros; try congruence.
      destruct path; eauto.
      destruct (tu_dispatch base (g :: path) fn) eqn:Heq.
      { destruct p. destruct p.
        apply IHpath in Heq. rewrite Heq. clear IHpath Heq.
        simpl in *.
        do 2 (case_match; try congruence).
        revert select (_ !! _ = _) => /glob_def_genv_compat_struct.
        unfold glob_def. move => ->. case_match; eauto. }
      { inversion H. }
    Qed.

  End tu.

End dispatch.
