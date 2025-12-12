(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export bluerock.prelude.elpi.derive.common.
Require Export Lens.Elpi.Elpi.
Require Lens.Lens.

Export Lens(Lens).
Export Lens.LensNotations.

Definition Lens_with {A B} (x : A) (f : A -> B) : B := f x.

Notation "a `with` b" :=
  (Lens_with a b)
  (at level 50, left associativity) : lens_scope.
Bind Scope lens_scope with Lens.
