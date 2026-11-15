Require Import stdpp.prelude.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.dispatch.
Require test_17_cpp.

#[local] Ltac check := vm_compute; reflexivity.

Definition overrides_of (tu : translation_unit) (cls : name) : option (list (obj_name * obj_name)) :=
  match tu.(types) !! cls with
  | Some (Gstruct st) => Some st.(s_overrides)
  | _ => None
  end.

(* [D] re-declares [C::g] as pure virtual; its override entry is still
   recorded, so dispatch on a [C*] to a complete [E] reaches [E::g]. *)
Example _overrides_D :
  overrides_of test_17_cpp.source "D"%cpp_name
  = Some [("C::g()"%cpp_name, "D::g()"%cpp_name)] := ltac:(check).

Example _dispatch_through_pure :
  dispatch.tu_dispatch test_17_cpp.source "C"%cpp_name ["E";"D";"C"]%cpp_name "C::g()"%cpp_name
  = Some ("E"%cpp_name, ["D";"C"]%cpp_name, "E::g()"%cpp_name) := ltac:(check).
