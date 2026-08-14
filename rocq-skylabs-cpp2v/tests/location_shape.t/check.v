Require Import skylabs.lang.cpp.syntax.source_location.
Require Import skylabs.lang.cpp.parser.
Require Import fixture_17_cpp_locations.

#[local] Open Scope pstring_scope.

Definition shape_root : decl_root :=
  DRSymbol
    (Nglobal
      (core.Nfunction function_qualifiers.N "shape"
        [Tnum int_rank.Iint Signed])).

Definition classes (result : lookup_error + list source_origin)
    : list origin_kind :=
  match result with
  | inr origins => List.map origin_class origins
  | inl _ => []
  end.

Definition lines (result : lookup_error + list source_origin)
    : list (option N) :=
  match result with
  | inr origins =>
      List.map (fun origin =>
        match origin.(spelling_range) with
        | Some range =>
            match range.(range_begin) with
            | Some point => Some point.(point_line)
            | None => None
            end
        | None => None
        end) origins
  | inl _ => []
  end.

Example grouped_condition_retains_erased_wrapper :
    classes
      (skylabs.lang.cpp.syntax.source_location.lookup source_locations
        shape_root [0; 2; 0; 1; 0]) =
      [ExplicitOrigin; ClangTransformedOrigin].
Proof. vm_compute. reflexivity. Qed.

Example multi_declaration_second_initializer :
    lines
      (skylabs.lang.cpp.syntax.source_location.lookup source_locations
        shape_root [0; 2; 0; 0; 1; 1]) = [Some 4%N].
Proof. vm_compute. reflexivity. Qed.

Example point_empty_synthesized_else_remains_in_the_tree :
  skylabs.lang.cpp.syntax.source_location.lookup source_locations
    shape_root [0; 2; 0; 1; 2] = inr [].
Proof. vm_compute. reflexivity. Qed.

Example second_call_argument_is_in_source_order :
    lines
      (skylabs.lang.cpp.syntax.source_location.lookup source_locations
        shape_root [0; 2; 0; 1; 1; 0; 2]) = [Some 6%N].
Proof. vm_compute. reflexivity. Qed.

Example absent_if_options_add_no_children :
    skylabs.lang.cpp.syntax.source_location.lookup source_locations
      shape_root [0; 2; 0; 1; 3] =
      inl (ChildOutOfBounds shape_root 4 3 3).
Proof. vm_compute. reflexivity. Qed.

Example declaration_list_has_exact_arity :
    skylabs.lang.cpp.syntax.source_location.lookup source_locations
      shape_root [0; 2; 0; 0; 2] =
      inl (ChildOutOfBounds shape_root 4 2 2).
Proof. vm_compute. reflexivity. Qed.
