(************************************************************************)
(* Parser/user-error cases for #[params="N"].                           *)
(************************************************************************)

Require Import attrs.ParamsAttr.

Fail #[params="-1"] Definition bad_neg := 0.
Fail #[params="abc"] Definition bad_abc := 0.
Fail #[params] Definition bad_empty := 0.
Fail #[params="0", params="1"] Definition bad_dup := 0.

(* #[params=0] is rejected by Rocq's attribute grammar before [Fail] can
   catch it, so it is covered by Rocq parsing rather than this compile test. *)
