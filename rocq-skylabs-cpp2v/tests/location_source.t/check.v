Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Import skylabs.lang.cpp.syntax.source_location.
Require Import skylabs.lang.cpp.parser.
Require Import fixture_17_cpp_locations.

#[local] Open Scope pstring_scope.

Definition user_root : decl_root :=
  DRSymbol
    (Nglobal
      (core.Nfunction function_qualifiers.N "user_header_value" [])).
Definition system_root : decl_root :=
  DRSymbol
    (Nglobal
      (core.Nfunction function_qualifiers.N "system_header_value" [])).
Definition pretending_header_root : decl_root :=
  DRSymbol
    (Nglobal
      (core.Nfunction function_qualifiers.N "header_pretends_main" [])).
Definition macro_root : decl_root :=
  DRSymbol
    (Nglobal
      (core.Nfunction function_qualifiers.N "nested_macro"
        [Tnum int_rank.Iint Signed])).
Definition line_root : decl_root :=
  DRSymbol
    (Nglobal
      (core.Nfunction function_qualifiers.N "line_mapped"
        [Tnum int_rank.Iint Signed])).
Definition absolute_line_root : decl_root :=
  DRSymbol
    (Nglobal
      (core.Nfunction function_qualifiers.N "absolute_line_mapped"
        [Tnum int_rank.Iint Signed])).

Definition found (root : decl_root) (path : loc_path)
    : lookup_error + list source_origin :=
  skylabs.lang.cpp.syntax.source_location.lookup source_locations root path.

Definition macro_names (origin : source_origin)
    : list (option PrimString.string) :=
  List.map macro_name origin.(macro_stack).
Definition stacks (root : decl_root) (path : loc_path)
    : list (list (option PrimString.string)) :=
  match found root path with
  | inr origins => List.map macro_names origins
  | inl _ => []
  end.

Definition range_lines
    (select : source_origin -> option source_range)
    (root : decl_root) (path : loc_path) : list (option PrimInt63.int) :=
  match found root path with
  | inr origins =>
      List.map (fun origin =>
        match select origin with
        | Some range =>
            match range.(range_begin) with
            | Some point => Some point.(point_line)
            | None => None
            end
        | None => None
        end) origins
  | inl _ => []
  end.

Definition physical_points (root : decl_root) (path : loc_path)
    : list (option (PrimInt63.int * PrimInt63.int * PrimInt63.int)) :=
  match found root path with
  | inr origins =>
      List.map (fun origin =>
        match origin.(spelling_range) with
        | Some range =>
            match range.(range_begin) with
            | Some point =>
                Some (point.(point_byte_offset), point.(point_line),
                      point.(point_byte_column))
            | None => None
            end
        | None => None
        end) origins
  | inl _ => []
  end.

Definition presumed (root : decl_root) (path : loc_path)
    : list (option (source_name * PrimInt63.int)) :=
  match found root path with
  | inr origins =>
      List.map (fun origin =>
        match origin.(presumed_begin) with
        | Some point => Some (point.(presumed_file), point.(presumed_line))
        | None => None
        end) origins
  | inl _ => []
  end.

Example header_only_roots_are_omitted :
  (found user_root [], found system_root [], found pretending_header_root []) =
    (inl (RootNotFound user_root), inl (RootNotFound system_root),
     inl (RootNotFound pretending_header_root)).
Proof. vm_compute. reflexivity. Qed.

Example header_line_directive_does_not_change_physical_membership :
  found pretending_header_root [] = inl (RootNotFound pretending_header_root).
Proof. vm_compute. reflexivity. Qed.

Example main_macro_drops_header_spelling_and_macro_frames :
  (stacks macro_root [0; 2; 0; 0; 0],
   range_lines spelling_range macro_root [0; 2; 0; 0; 0],
   range_lines expansion_range macro_root [0; 2; 0; 0; 0]) =
    ([[]; []], [None; None], [Some 4%uint63; Some 4%uint63]).
Proof. vm_compute. reflexivity. Qed.

Example line_directive_preserves_physical_point :
  physical_points line_root [0; 2; 0; 0; 0] =
    [Some (176%uint63, 7%uint63, 37%uint63)].
Proof. vm_compute. reflexivity. Qed.

Example line_directive_preserves_presumed_point :
  presumed line_root [0; 2; 0; 0; 0] =
    [Some (LiteralSourceName "logical.cpp", 700%uint63)].
Proof. vm_compute. reflexivity. Qed.

Example absolute_line_directive_remains_literal_text :
  presumed absolute_line_root [0; 2; 0; 0; 0] =
    [Some (LiteralSourceName "/logical/absolute.cpp", 800%uint63)].
Proof. vm_compute. reflexivity. Qed.

Example default_companion_has_only_the_main_file :
  List.length source_locations.(files) = 1.
Proof. vm_compute. reflexivity. Qed.
