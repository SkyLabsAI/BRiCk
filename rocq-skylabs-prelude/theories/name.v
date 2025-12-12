(**
 * Copyright (C) 2023 BlueRock Security, Inc.
 * All rights reserved.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use
 * over network, see repository root for details.
 *)
Require Import bluerock.prelude.finite.

Class Names (T : Set) := mkNames {
  #[global] name_eq_dec :: EqDecision T ;
  #[global] name_finite :: Finite T ;
  #[global] name_inhabited :: Inhabited T ;
}.
#[global] Hint Mode Names + : typeclass_instances.

Class PossiblyEmptyNames (T : Set) := mkPossiblyEmptyNames {
  #[global] pe_name_eq_dec :: EqDecision T ;
  #[global] pe_name_finite :: Finite T ;
}.
#[global] Hint Mode PossiblyEmptyNames + : typeclass_instances.
