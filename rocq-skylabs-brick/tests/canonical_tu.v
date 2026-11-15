Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.model.simple_pointers_utils.
Module Canon := skylabs.lang.cpp.model.simple_pointers_utils.canonical_tu.

Definition integer_global : ObjValue := Ovar "int" global_init.Extern.
Definition boolean_global : ObjValue := Ovar "bool" global_init.Extern.
Definition symbols_forward : symbol_table :=
  <["one::value"%cpp_name := integer_global]>
    (<["two::value"%cpp_name := boolean_global]> ∅).
Definition symbols_reverse : symbol_table :=
  <["two::value"%cpp_name := boolean_global]>
    (<["one::value"%cpp_name := integer_global]> ∅).
Definition source (syms : symbol_table) : translation_unit :=
  makeTranslationUnit syms (<["one::Record"%cpp_name := Gtype]> ∅)
    ∅ [] [] abi.abi_default ∅ ∅ ∅ ∅.

Lemma canonical_namespaces_distinct :
  Canon.tu_to_canon (source symbols_forward) !! "one::value"%cpp_name = Some integer_global /\
  Canon.tu_to_canon (source symbols_forward) !! "two::value"%cpp_name = Some boolean_global.
Proof. vm_compute. split; reflexivity. Qed.

Lemma canonical_missing_name :
  Canon.tu_to_canon (source symbols_forward) !! "three::value"%cpp_name = None.
Proof. vm_compute. reflexivity. Qed.

Lemma canonical_insertion_order :
  Canon.tu_to_canon (source symbols_forward) = Canon.tu_to_canon (source symbols_reverse).
Proof. vm_compute. reflexivity. Qed.

Lemma canonical_types_preserved tu :
  Canon.globals (Canon.tu_to_canon tu) = NM.elements tu.(translation_unit.types).
Proof. reflexivity. Qed.

Lemma canonical_abi_preserved tu :
  Canon.abi (Canon.tu_to_canon tu) = tu.(translation_unit.abi).
Proof. reflexivity. Qed.
