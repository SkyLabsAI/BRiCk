Require Import skylabs.lang.cpp.model.simple_pred.

(** The implementation must not assume the fraction-validity law it proves. *)
Set Printing Fully Qualified.
Print Assumptions SimpleCPP.mdc_path_cfrac_valid.
Print Assumptions SimpleCPP.type_ptr_erase.

(** Affinity follows from the concrete logic; it needs no exposure axiom. *)
Print Assumptions SimpleCPP.exposed_aid_affine.

(** The unused model-only helper chain and its duplicate axiom stay absent. *)
Fail Check SimpleCPP.pinned_ptr_type_divide_2.
Fail Check SimpleCPP.valid_type_uchar.
Fail Check SimpleCPP.align_of_uchar.
