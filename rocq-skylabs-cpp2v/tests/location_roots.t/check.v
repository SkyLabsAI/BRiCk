Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Import skylabs.lang.cpp.syntax.source_location.
Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.mparser.
Require Import fixture_17_cpp_locations.

#[local] Open Scope pstring_scope.

Definition int_type : type := Tnum int_rank.Iint Signed.
Definition self_type : decl_root := DRType (Nglobal (Nid "Self")).
Definition twice_symbol : decl_root :=
  DRSymbol
    (Nscoped (Nglobal (Nid "Ordinary"))
      (core.Nfunction function_qualifiers.N "twice" [int_type])).
Definition default_ctor : decl_root :=
  DRSymbol (Nscoped (Nglobal (Nid "Ordinary")) (core.Nctor [])).
Definition enum_constant : decl_root :=
  DRType (Nscoped (Nglobal (Nid "Kind")) (Nid "Value")).
Definition box_int_name : name :=
  Ninst (Nglobal (Nid "Box")) [Atype int_type].
Definition box_int_type : decl_root := DRType box_int_name.
Definition box_pattern_name : name :=
  Ninst (Nglobal (Nid "Box")) [Atype (Tparam "T")].
Definition box_pattern_type : decl_root := DRMtype box_pattern_name.
Definition identity_int : decl_root :=
  DRSymbol
    (Ninst
      (Nglobal
        (core.Nfunction function_qualifiers.N "identity" [int_type]))
      [Atype int_type]).
Definition identity_pattern : decl_root :=
  DRMsymbol
    (Ninst
      (Nglobal
        (core.Nfunction function_qualifiers.N "identity" [Tparam "T"]))
      [Atype (Tparam "T")]).
Definition selected_symbol : decl_root :=
  DRSymbol
    (Nglobal
      (core.Nfunction function_qualifiers.N "selected" [int_type])).

Definition found (root : decl_root) (path : loc_path)
    : lookup_error + list source_origin :=
  skylabs.lang.cpp.syntax.source_location.lookup source_locations root path.
Definition present (root : decl_root) : bool :=
  match found root [] with inr _ => true | inl _ => false end.
Definition classes (root : decl_root) (path : loc_path)
    : list origin_kind :=
  match found root path with
  | inr origins => List.map origin_class origins
  | inl _ => []
  end.
Definition spelling_lines (root : decl_root) (path : loc_path)
    : list (option PrimInt63.int) :=
  match found root path with
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
Definition links (root : decl_root) (path : loc_path)
    : list (bool * nat) :=
  match found root path with
  | inr origins =>
      List.map (fun origin =>
        (match origin.(anchor_origin) with
         | Some _ => true
         | None => false
         end,
         List.length origin.(derived_from))) origins
  | inl _ => []
  end.
Definition pois (root : decl_root) (path : loc_path)
    : list (option (PrimInt63.int * PrimInt63.int)) :=
  match found root path with
  | inr origins =>
      List.map (fun origin =>
        match origin.(point_of_instantiation) with
        | Some point => Some (point.(point_line), point.(point_byte_column))
        | None => None
        end) origins
  | inl _ => []
  end.

Example all_four_root_namespaces_are_populated :
    (present selected_symbol, present self_type,
     present identity_pattern, present box_pattern_type) =
      (true, true, true, true).
Proof. vm_compute. reflexivity. Qed.

Example namespaces_do_not_cross_lookup :
    (present (DRType box_pattern_name), present (DRMtype box_int_name)) =
      (false, false).
Proof. vm_compute. reflexivity. Qed.

Example static_method_is_final_transformed_function :
    (classes twice_symbol [], links twice_symbol []) =
      ([ExplicitOrigin; ClangTransformedOrigin],
       [(false, 0); (false, 1)]).
Proof. vm_compute. reflexivity. Qed.

Example implicit_member_is_distinguishable :
    classes default_ctor [] = [ImplicitOrigin].
Proof. vm_compute. reflexivity. Qed.

Example closure_only_enum_value_origin_is_not_attached :
  found enum_constant [1] = inr [].
Proof. vm_compute. reflexivity. Qed.

Example compatible_definition_is_the_selected_root :
    spelling_lines selected_symbol [] = [Some 22%uint63].
Proof. vm_compute. reflexivity. Qed.

Example self_typedef_does_not_replace_the_record :
    spelling_lines self_type [] = [Some 3%uint63].
Proof. vm_compute. reflexivity. Qed.

Example class_specialization_keeps_separate_poi :
    pois box_int_type [] = [Some (25%uint63, 9%uint63)].
Proof. vm_compute. reflexivity. Qed.

Example function_specialization_keeps_separate_poi :
    pois identity_int [] = [Some (26%uint63, 10%uint63)].
Proof. vm_compute. reflexivity. Qed.

Example template_parameter_default_precedes_value :
    (spelling_lines box_pattern_type [0],
     spelling_lines box_pattern_type [1],
     spelling_lines box_pattern_type [2]) =
      ([Some 14%uint63], [Some 14%uint63], [Some 14%uint63]).
Proof. vm_compute. reflexivity. Qed.

Example template_root_has_exact_parameter_default_value_arity :
    found box_pattern_type [3] =
      inl (ChildOutOfBounds box_pattern_type 0 3 3).
Proof. vm_compute. reflexivity. Qed.
