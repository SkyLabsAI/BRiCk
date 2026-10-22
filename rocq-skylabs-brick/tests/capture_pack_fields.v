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
