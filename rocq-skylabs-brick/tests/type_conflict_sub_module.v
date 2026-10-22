Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.lang.cpp.semantics.sub_module.

(** * Appending and prepending code, and [sub_module]

The first cases below use field-based names, without the fallback anonymous
indices introduced to distinguish collisions within one declaration context.
For these cases, adding a separate namespace block preserves the original
module unless it defines an incompatible type under a name already used.
Incompatible definitions are quarantined as [Gunsupported] in either order.

These examples do not establish a general composition property. In particular,
fallback indices count across reopened namespace blocks: appending the unrelated
block in the final example preserves [sub_module], but prepending it renumbers
an existing type and breaks [sub_module]. *)

cpp.prog a prog cpp:{{
  namespace N { struct { int a; } *p; }
}}.

(** ** No collision: appending and prepending preserve [sub_module] *)

cpp.prog a_c prog cpp:{{
  namespace N { struct { int a; } *p; }
  namespace N { struct { char c; } *r; }
}}.

cpp.prog c_a prog cpp:{{
  namespace N { struct { char c; } *r; }
  namespace N { struct { int a; } *p; }
}}.

Example append_unrelated : bool_decide (sub_module a a_c) = true.
Proof. vm_compute. reflexivity. Qed.

Example prepend_unrelated : bool_decide (sub_module a c_a) = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Compatible collision: the definitions merge *)

cpp.prog a_a prog cpp:{{
  namespace N { struct { int a; } *p; }
  namespace N { struct { int a; } *p2; }
}}.

Example append_compatible : bool_decide (sub_module a a_a) = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Incompatible collision: the type is quarantined *)

cpp.prog a_b prog cpp:{{
  namespace N { struct { int a; } *p; }
  namespace N { struct { long a; } *q; }
}}.

cpp.prog b_a prog cpp:{{
  namespace N { struct { long a; } *q; }
  namespace N { struct { int a; } *p; }
}}.

Definition is_unsupported (tu : translation_unit) (n : name) : bool :=
  if tu.(types) !! n is Some (Gunsupported _) then true else false.

Example append_conflict_unsupported : is_unsupported a_b "N::.a"%cpp_name = true.
Proof. vm_compute. reflexivity. Qed.

Example prepend_conflict_unsupported : is_unsupported b_a "N::.a"%cpp_name = true.
Proof. vm_compute. reflexivity. Qed.

(** Neither the appended nor the prepended conflicting definition lets [a]'s
    facts about [N::.a] carry over. *)
Example append_conflict : bool_decide (sub_module a a_b) = false.
Proof. vm_compute. reflexivity. Qed.

Example prepend_conflict : bool_decide (sub_module a b_a) = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Fallback names: prepending can renumber an existing type

The two unnamed records in the first block compete for the field-based name
[N::.a]. The second therefore uses its anonymous index, [N::@1]. Adding an
unrelated unnamed record before that block changes the index to [N::@2], even
though it occurs in a separate block of the reopened namespace. *)

cpp.prog fallback prog cpp:{{
  namespace N { struct { int a; } *p; struct { long a; } *q; }
}}.

cpp.prog fallback_append prog cpp:{{
  namespace N { struct { int a; } *p; struct { long a; } *q; }
  namespace N { struct {} *seed; }
}}.

cpp.prog fallback_prepend prog cpp:{{
  namespace N { struct {} *seed; }
  namespace N { struct { int a; } *p; struct { long a; } *q; }
}}.

Definition variable_type (tu : translation_unit) (n : name) : option type :=
  type_of_value <$> tu.(symbols) !! n.

Example fallback_q_type :
  variable_type fallback "N::q"%cpp_name = Some "N::@1*"%cpp_type.
Proof. vm_compute. reflexivity. Qed.

Example fallback_append_q_type :
  variable_type fallback_append "N::q"%cpp_name = Some "N::@1*"%cpp_type.
Proof. vm_compute. reflexivity. Qed.

Example fallback_prepend_q_type :
  variable_type fallback_prepend "N::q"%cpp_name = Some "N::@2*"%cpp_type.
Proof. vm_compute. reflexivity. Qed.

Example append_after_fallback :
  bool_decide (sub_module fallback fallback_append) = true.
Proof. vm_compute. reflexivity. Qed.

Example prepend_before_fallback :
  bool_decide (sub_module fallback fallback_prepend) = false.
Proof. vm_compute. reflexivity. Qed.
