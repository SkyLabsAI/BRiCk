Require test.test_cpp.
Require test.test_no_preprint_cpp.

Goal test_cpp.module = test_no_preprint_cpp.module.
Proof. vm_compute; reflexivity. Qed.
