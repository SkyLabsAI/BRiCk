Require Import skylabs.lang.cpp.syntax.source_location.
Require Import skylabs.lang.cpp.parser.
Require Import all_files_locations.

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

Definition found (root : decl_root) (path : loc_path) : list source_origin :=
  match skylabs.lang.cpp.syntax.source_location.lookup
          source_locations root path with
  | inr origins => origins
  | inl _ => []
  end.

Definition macro_names (origin : source_origin)
    : list (option PrimString.string) :=
  List.map macro_name origin.(macro_stack).
Definition stacks (root : decl_root) (path : loc_path)
    : list (list (option PrimString.string)) :=
  List.map macro_names (found root path).

Definition range_lines
    (select : source_origin -> option source_range)
    (root : decl_root) (path : loc_path) : list (option N) :=
  List.map (fun origin =>
    match select origin with
    | Some range =>
        match range.(range_begin) with
        | Some point => Some point.(point_line)
        | None => None
        end
    | None => None
    end) (found root path).

Definition file_of (root : decl_root) : option source_file :=
  match found root [] with
  | origin :: _ =>
      match origin.(spelling_range) with
      | Some range =>
          match range.(range_begin) with
          | Some point => lookup_file source_locations point.(point_file)
          | None => None
          end
      | None => None
      end
  | [] => None
  end.

Definition file_fact (root : decl_root)
    : option (file_kind * bool * option (file_id * N)) :=
  match file_of root with
  | Some file =>
      Some (file.(source_file_kind), file.(source_file_is_main),
            file.(source_file_include_parent))
  | None => None
  end.

Example nested_macro_frames_are_nearest_first :
  stacks macro_root [0; 2; 0; 0; 0] =
    [[Some "USER_INNER"; Some "USER_OUTER"];
     [Some "USER_INNER"; Some "USER_OUTER"]].
Proof. vm_compute. reflexivity. Qed.

Example macro_spelling_and_expansion_are_distinct :
  (range_lines spelling_range macro_root [0; 2; 0; 0; 0],
   range_lines expansion_range macro_root [0; 2; 0; 0; 0]) =
    ([Some 2%N; Some 2%N], [Some 4%N; Some 4%N]).
Proof. vm_compute. reflexivity. Qed.

Example user_header_keeps_include_parent :
  file_fact user_root = Some (FKUser, false, Some (0%file_id, 9%N)).
Proof. vm_compute. reflexivity. Qed.

Example system_header_keeps_kind_and_parent :
  file_fact system_root =
    Some (FKSystem, false, Some (0%file_id, 36%N)).
Proof. vm_compute. reflexivity. Qed.

Example header_line_directive_does_not_change_physical_file :
  file_fact pretending_header_root =
    Some (FKUser, false, Some (0%file_id, 9%N)).
Proof. vm_compute. reflexivity. Qed.

Example files_are_in_first_seen_order : List.length source_locations.(files) = 3.
Proof. vm_compute. reflexivity. Qed.
