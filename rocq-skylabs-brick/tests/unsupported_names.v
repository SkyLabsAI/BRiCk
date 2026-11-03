Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import stdpp.fin_maps.

(** * Names that may denote several entities

cpp2v prints some names with an unsupported atom: an unnamed struct at global
scope is [?record], and a floating-point template argument is
[Aunsupported "<unknown>"]. Distinct entities can then share one name, and
equal definitions would merge, so [v<decltype(p)>] and [v<decltype(q)>] below
would be one global. [cpp.prog] therefore drops every symbol whose name
contains an unsupported atom ([has_unsupportedN]), and makes every such type
[Gunsupported]. *)

cpp.prog tu flags "-std=c++20" prog cpp:{{
  struct { int a; } *p;
  struct { int a; } *q;
  template <class T> char v = 0;
  template <double D> char w = 0;
  char *r = &v<decltype(p)>;
  char *s = &v<decltype(q)>;
  char *t = &w<1.0>;
  char *u = &w<2.0>;
}}.

Example no_unsupported_symbol :
  List.existsb (fun kv => has_unsupportedN kv.1) (map_to_list tu.(symbols)) = false.
Proof. vm_compute. reflexivity. Qed.

(** The types named [?record] are there, but unsupported. *)
Example unsupported_type_present :
  List.existsb (fun kv => has_unsupportedN kv.1) (map_to_list tu.(types)) = true.
Proof. vm_compute. reflexivity. Qed.

Example unsupported_types_quarantined :
  List.forallb (fun kv => negb (has_unsupportedN kv.1) || if kv.2 is Gunsupported _ then true else false)
    (map_to_list tu.(types)) = true.
Proof. vm_compute. reflexivity. Qed.

(** Symbols with ordinary names are kept. *)
Example ordinary_symbols_kept :
  is_Some (tu.(symbols) !! "r"%cpp_name) /\ is_Some (tu.(symbols) !! "t"%cpp_name).
Proof. split; vm_compute; eexists; reflexivity. Qed.
