Require test.test_cpp.
Require test.test_no_preprint_cpp.

Goal test_cpp.source = test_no_preprint_cpp.source.
Proof. vm_compute; reflexivity. Qed.
