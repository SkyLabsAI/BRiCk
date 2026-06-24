Require Import skylabs.lang.cpp.syntax.

Require test.x64.
Require test.aarch64.

Goal x64.source.(abi) =
  abi.mkT int_rank.Ilong Signed Signed Little lang_version.Cpp17.
Proof. vm_compute; reflexivity. Qed.

Goal aarch64.source.(abi) =
  abi.mkT int_rank.Ilong Unsigned Unsigned Little lang_version.Cpp17.
Proof. vm_compute; reflexivity. Qed.
