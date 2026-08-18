Require Import Ltac2.Ltac2.
Require Import skylabs.ltac2.logger.logger.
Import Printf Log.

Ltac2 Log Flag test.
Ltac2 Dev Log Flag dev.

Ltac2 test () :=
  log[test,0] "%s,%i,%I\n%m\n%a\n"
    "test_string"
    42
    @test_ident
    (fprintf "msg")
    Log.pp_ast 'True.

Ltac2 test_filter () :=
  log[test,0]  "test 0";
  log[test]    "test";
  log[test,1]  "test 1";
  log[test,10] "test 10";
  log[dev,0]   "dev 0";
  log[dev]     "dev";
  log[dev,1]   "dev 1";
  log[dev,10]  "dev 1";
  log[test,0] "\n".

Set SL Debug "_=1".

Goal True.
Proof.
  reset_log ();
  test ();
  output_log ().
  test ();
  output_log ().
  reset_log ().
  exact I.
Qed.

Goal True.
Proof.
  with_log true None test.
  exact I.
Qed.

Goal True.
Proof.
  with_log true None test_filter.
  Set SL Debug "*=1".
  with_log true None test_filter.
  Set SL Debug "_=10".
  with_log true None test_filter.
  Set SL Debug "*=10".
  with_log true None test_filter.
  exact I.
Qed.

Goal True.
Proof.
  Set SL Direct Log.
  test ().
  reset_log ().
  exact I.
Qed.
