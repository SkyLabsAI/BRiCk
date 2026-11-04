Require Import skylabs.lang.cpp.cpp.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.

(** BRiCk identifies a field by its name, so the fields of a closure need
    distinct names. Each element of a capture pack gets its own field, named
    [vs], [vs...1], ... in field order. *)
cpp.prog source flags "-std=c++20" prog cpp:{{
  template<int... Vs>
  int init_pack(int x) {
    auto l = [x, ...vs = Vs]() { return x + (vs + ...); };
    return l();
  }

  template<class... T>
  int copy_pack(T... vs) {
    auto l = [vs...]() { return (vs + ...); };
    return l();
  }

  int test() { return init_pack<1, 2, 3>(0) + copy_pack(1, 2); }
}}.

Definition field_names (cls : name) : list field_name :=
  match source.(types) !! cls with
  | Some (Gstruct s) => mem_name <$> s.(s_fields)
  | _ => []
  end.

Goal field_names "init_pack<...<1, 2, 3>>(int)::@0" =
  [Nid "x"; Nid "vs"; Nid "vs...1"; Nid "vs...2"].
Proof. by vm_compute. Qed.

Goal field_names "copy_pack<...<int, int>>(int, int)::@0" = [Nid "vs"; Nid "vs...1"].
Proof. by vm_compute. Qed.

(** A record whose fields do not have distinct names is unsupported. *)
Definition int_member (n : ident) (off : N) : Member :=
  {| mem_name := Nid n; mem_type := Tint; mem_mutable := false;
     mem_init := None; mem_layout := {| li_offset := off |} |}.

Definition S_struct (fs : list Member) : Struct :=
  Build_Struct [] fs [] [] "S::~S()"%cpp_name true None POD 8 4.

Definition S_decl (fs : list Member) : option GlobDecl :=
  (fst (parser.translation_unit.list_decls
          [parser.Dstruct "S" (Some (S_struct fs))] abi.abi_default)).(types) !! "S"%cpp_name.

Goal S_decl [int_member "a" 0; int_member "b" 32] =
  Some (Gstruct (S_struct [int_member "a" 0; int_member "b" 32])).
Proof. by vm_compute. Qed.

Goal if S_decl [int_member "a" 0; int_member "a" 32] is Some (Gunsupported _)
     then True else False.
Proof. by vm_compute. Qed.

(** Records with more than 16 fields are checked by sorting. *)
Definition many_members (names : list ident) : list Member :=
  zip_with int_member names (N.of_nat <$> seq 0 (length names)).
Definition letters : list ident :=
  ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"; "l"; "m"; "n"; "o"; "p"; "q"]%pstring.

Goal S_decl (many_members letters) = Some (Gstruct (S_struct (many_members letters))).
Proof. by vm_compute. Qed.

Goal if S_decl (many_members (letters ++ ["i"%pstring])) is Some (Gunsupported _)
     then True else False.
Proof. by vm_compute. Qed.
