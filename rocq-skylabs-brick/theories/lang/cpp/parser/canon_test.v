(*
 * Copyright (c) 2026 Abhishek Anand.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import skylabs.lang.cpp.parser.

Set Default Goal Selector "!".

(** Canonicalization changes only the AVL proof, not the tree or its lookups. *)
Lemma map_canon_preserves_tree {A : Type} (m : NM.t A) :
  NM.this (NM.map_canon m) = NM.this m.
Proof.
  unfold NM.map_canon, NM.from_raw_or.
  generalize (NM.check_canon_ok (NM.this m)).
  destruct (NM.check_canon None None (NM.this m)); intros; reflexivity.
Qed.

Lemma map_canon_preserves_lookup {A : Type} (m : NM.t A) (n : name) :
  NM.find n (NM.map_canon m) = NM.find n m.
Proof.
  change (NM.Raw.find n (NM.this (NM.map_canon m)) = NM.Raw.find n (NM.this m)).
  rewrite map_canon_preserves_tree. reflexivity.
Qed.

(** Normalize the whole result, including its proof fields. Computing only
    lookups would discard those fields and miss the reification regression. *)
Definition fixture : translation_unit * translation_unit.dup_info :=
  Eval vm_compute in translation_unit.list_decls
    [translation_unit._symbols "kept"%cpp_name
       (translation_unit.conflict "untouched_payload"%cpp_name);
     translation_unit._symbols "collision"%cpp_name
       (translation_unit.conflict "first"%cpp_name);
     translation_unit._symbols "collision"%cpp_name
       (translation_unit.conflict "second"%cpp_name)]
    abi.abi_default.

Example collision_is_replaced :
  fixture.1.(symbols) !! "collision"%cpp_name =
    Some (translation_unit.conflict "collision"%cpp_name).
Proof. reflexivity. Qed.

Example unrelated_symbol_is_preserved :
  fixture.1.(symbols) !! "kept"%cpp_name =
    Some (translation_unit.conflict "untouched_payload"%cpp_name).
Proof. reflexivity. Qed.

(** This fails if the parser retains the insertion-proof chain. *)
Example symbol_proof_is_canonical :
  NM.is_bst fixture.1.(symbols) =
    NM.check_canon_ok (NM.this fixture.1.(symbols)) I.
Proof. reflexivity. Qed.
