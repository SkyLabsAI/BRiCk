Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.syntax.mcore.
Require Import skylabs.lang.cpp.semantics.types.
Require test.test_cpp.

(* Uninstantiated static-member definitions are template metadata, not objects
   in the ordinary translation unit. Actual specializations remain objects. *)
Example pattern_not_runtime :
  test_cpp.source.(symbols) !! "Test::Holder<$T>::value"%cpp_name = None.
Proof. vm_compute. reflexivity. Qed.

Example pattern_preserved :
  is_Some (test_cpp.source.(msymbols) !! "Test::Holder<$T>::value"%cpp_name).
Proof. vm_compute. eexists. reflexivity. Qed.

Example specialization_preserved :
  match test_cpp.source.(symbols) !! "Test::Holder<int>::value"%cpp_name with
  | Some (Ovar ty _) => erase_qualifiers ty = Tint
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

Definition zero_layout (g : GlobDecl) : bool :=
  match g with
  | Gstruct st => N.eqb st.(s_size) 0 || N.eqb st.(s_alignment) 0
  | _ => false
  end.

Example no_runtime_placeholders :
  List.filter (fun entry => zero_layout entry.2) (TM.elements test_cpp.source.(types)) = [].
Proof. vm_compute. reflexivity. Qed.

Example template_records_preserved :
  length (List.filter (fun entry => zero_layout entry.2.(template_value))
    (TM.elements test_cpp.source.(mtypes))) = 2%nat.
Proof. vm_compute. reflexivity. Qed.

Example instantiated_closure_layout :
  match test_cpp.source.(symbols) !! "Test::actual_closure"%cpp_name with
  | Some (Ovar (Tnamed cls) _) =>
      match test_cpp.source.(types) !! cls with
      | Some (Gstruct st) => (st.(s_size), st.(s_alignment)) = (1%N, 1%N)
      | _ => False
      end
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.
