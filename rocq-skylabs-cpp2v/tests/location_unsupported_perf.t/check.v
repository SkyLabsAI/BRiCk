Require Import skylabs.lang.cpp.syntax.source_location.
Require Import skylabs.lang.cpp.parser.
Require Import fixture_17_cpp_locations.

#[local] Open Scope pstring_scope.

Definition unsupported_root : decl_root :=
  DRSymbol (Nglobal (Nid "unsupported_value")).
Definition builtin_root : decl_root := DRType (Nglobal (Nid "__int128_t")).
Definition found (root : decl_root) (path : loc_path)
    : lookup_error + list source_origin :=
  skylabs.lang.cpp.syntax.source_location.lookup source_locations root path.
Definition facts (root : decl_root) (path : loc_path)
    : list (origin_kind * (bool * bool)) :=
  match found root path with
  | inr origins =>
      List.map (fun origin =>
        (origin.(origin_class),
         match origin.(spelling_range) with
         | Some range =>
             (match range.(range_begin) with
              | Some _ => true
              | None => false
              end,
              match range.(range_end) with
              | Some _ => true
              | None => false
              end)
         | None => (false, false)
         end)) origins
  | inl _ => []
  end.

Example unsupported_type_keeps_written_range :
    facts unsupported_root [0] = [(ExplicitOrigin, (true, true))].
Proof. vm_compute. reflexivity. Qed.

Example unsupported_expression_keeps_written_range :
    facts unsupported_root [1; 0] = [(ExplicitOrigin, (true, true))].
Proof. vm_compute. reflexivity. Qed.

Example unsupported_expression_type_is_inherited :
    facts unsupported_root [1; 0; 0] = [(InheritedOrigin, (false, false))].
Proof. vm_compute. reflexivity. Qed.

Example implicit_builtin_location_is_representable :
    facts builtin_root [] = [(ImplicitOrigin, (false, false))].
Proof. vm_compute. reflexivity. Qed.

Example independently_rangeless_builtin_child_is_representable :
    facts builtin_root [0] = [(ExplicitOrigin, (false, false))].
Proof. vm_compute. reflexivity. Qed.
