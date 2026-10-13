Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.types.
Require test.test_cpp.

Definition global_type (nm : name) : option type :=
  match test_cpp.source.(symbols) !! nm with
  | Some (Ovar ty _) => Some (erase_qualifiers ty)
  | _ => None
  end.

Definition global_layout (nm : name) : option (N * N) :=
  match global_type nm with
  | Some (Tnamed cls) =>
      match test_cpp.source.(types) !! cls with
      | Some (Gstruct st) => Some (st.(s_size), st.(s_alignment))
      | _ => None
      end
  | _ => None
  end.

(* Query the actual global declarations, rather than assuming anonymous keys. *)
Example closure_classes_distinct :
  global_type "N::first"%cpp_name <> global_type "N::second"%cpp_name.
Proof. vm_compute. discriminate. Qed.

Example empty_closure_layout : global_layout "N::first"%cpp_name = Some (1%N, 1%N).
Proof. vm_compute. reflexivity. Qed.

Example captured_closure_layout : global_layout "N::second"%cpp_name = Some (4%N, 4%N).
Proof. vm_compute. reflexivity. Qed.
