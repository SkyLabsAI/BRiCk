Require Import skylabs.prelude.base.
Require Import skylabs.prelude.arith.types.
Require Import skylabs.prelude.arith.operator.
Require Import skylabs.prelude.arith.builtins.
#[local] Open Scope Z_scope.

Example clz_42 : leading_zeros bitsize.W32 42 = 26.
Proof. vm_compute. reflexivity. Qed.
Example clz_one_all_widths :
  leading_zeros bitsize.W8 1 = 7 /\
  leading_zeros bitsize.W16 1 = 15 /\
  leading_zeros bitsize.W32 1 = 31 /\
  leading_zeros bitsize.W64 1 = 63 /\
  leading_zeros bitsize.W128 1 = 127.
Proof. vm_compute. repeat split; reflexivity. Qed.
Example clz_high_bits :
  leading_zeros bitsize.W8 (2^7) = 0 /\
  leading_zeros bitsize.W16 (2^15) = 0 /\
  leading_zeros bitsize.W32 (2^31) = 0 /\
  leading_zeros bitsize.W64 (2^63) = 0 /\
  leading_zeros bitsize.W128 (2^127) = 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Example clz_width_trimming :
  leading_zeros bitsize.W8 (2^64+1) = 7 /\
  leading_zeros bitsize.W32 (2^64+42) = 26 /\
  leading_zeros bitsize.W16 (-1) = 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Example clz_zero_helper_convention : forall sz, leading_zeros sz 0 = bitsize.bitsZ sz.
Proof. intros []; vm_compute; reflexivity. Qed.

Set Printing Fully Qualified.
Print Assumptions leading_zeros_spec.
Print Assumptions clz_42.
Print Assumptions clz_one_all_widths.
Print Assumptions clz_high_bits.
Print Assumptions clz_width_trimming.
Print Assumptions clz_zero_helper_convention.
