Require Import skylabs.lang.cpp.semantics.
Require test.inc_cpp test.src_cpp.

Set Default Goal Selector "!".

Definition members (tu : translation_unit) :=
  match tu.(types) !! "Box<unsigned long>"%cpp_name with
  | Some (Gstruct s) => s.(s_fields)
  | _ => []
  end.

Example same_members : members inc_cpp.source = members src_cpp.source.
Proof. vm_compute. reflexivity. Qed.

Example header_types_in_client :
  bool_decide (type_table_le inc_cpp.source.(types) src_cpp.source.(types)) = true.
Proof. vm_compute. reflexivity. Qed.

Example literal_defaults :
  map mem_init (members inc_cpp.source) =
    [Some (Ecast (Cintegral Tulong) (Eint 0 Tint)); Some (Ebool false); None].
Proof. vm_compute. reflexivity. Qed.
