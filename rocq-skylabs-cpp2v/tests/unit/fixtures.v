(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From Stdlib Require Import Lists.List.

(** Smoke-environment definitions for registry entries explicitly marked
    [testOnly]. They exercise generic Value grouping and are never legal IR
    roots or non-root event payloads. *)
Definition IR_optional {A : Type} (value : option A) : option A := value.
Definition IR_sequence {A : Type} (value : list A) : list A := value.
Definition IR_product {A B : Type} (value : A * B) : A * B := value.
Definition IR_sum {A B : Type} (value : A + B) : A + B := value.
Definition IR_ident_type_list {A B : Type} (value : list (A * B))
    : list (A * B) := value.
Definition IR_name_option_name_list {A : Type}
    (value : list (A * option A)) : list (A * option A) := value.
Definition IR_structure_virtuals {A : Type}
    (value : list (A * option A)) : list (A * option A) := value.
Definition IR_structure_overrides {A : Type}
    (value : list (A * A)) : list (A * A) := value.
Definition IR_OPAQUE {A : Type} (value : A) : A := value.
