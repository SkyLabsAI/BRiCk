Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.

Require test.test_cpp.

Example trivial_abi_unsupported :
  types test_cpp.source !! "TrivialABI"%cpp_name =
    Some (Gunsupported "trivial_abi classes are not supported").
Proof. vm_compute. reflexivity. Qed.

(* Virtual bases are supported (as [Gvstruct]), but the bit-field is not:
   the class stays unsupported rather than becoming an opaque record. *)
Example virtual_base_unsupported :
  types test_cpp.source !! "VirtualBase"%cpp_name =
    Some (Gunsupported "bitfields are not supported").
Proof. vm_compute. reflexivity. Qed.

(* Opaque records still expose size, alignment and lifetime metadata when
   only the hidden field/base layout is unsupported. *)
Definition opaque_reason (n : globname) : option PrimString.string :=
  match types test_cpp.source !! n with
  | Some (Gopaque o) => Some o.(o_reason)
  | _ => None
  end.

Example hidden_layout_opaque :
  opaque_reason <$> ["Plain"; "PackedClass"; "PackedReference"; "PackedBase"]%cpp_name =
    replicate 4 (Some "bitfields are not supported"%pstring).
Proof. vm_compute. reflexivity. Qed.
