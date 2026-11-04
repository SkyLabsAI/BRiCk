Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.lang.cpp.semantics.sub_module.

(** * Appending and prepending code, and [sub_module]

cpp2v names an unnamed record after its first named field, unless an earlier
unnamed record in the same naming context already has that name; it then falls
back to the record's anonymous index. All blocks of a reopened namespace form
one naming context, for both the collision check and the index.

Appending a namespace block therefore preserves [sub_module]: names in the
earlier blocks do not depend on later ones. Prepending a block does not, in
general: a type that collides with one in the new block, or any type named by
its index, can be renamed.

These examples do not establish a general composition property. *)

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

(** ** Colliding definitions get distinct names

Two distinct unnamed records with first field [a] in separate blocks are not
merged, even when their definitions agree: the later one is [N::@1]. *)

cpp.prog a_a prog cpp:{{
  namespace N { struct { int a; } *p; }
  namespace N { struct { int a; } *p2; }
}}.

cpp.prog a_b prog cpp:{{
  namespace N { struct { int a; } *p; }
  namespace N { struct { long a; } *q; }
}}.

cpp.prog b_a prog cpp:{{
  namespace N { struct { long a; } *q; }
  namespace N { struct { int a; } *p; }
}}.

Definition variable_type (tu : translation_unit) (n : name) : option type :=
  type_of_value <$> tu.(symbols) !! n.

Example compatible_distinct :
  variable_type a_a "N::p2"%cpp_name = Some "N::@1*"%cpp_type.
Proof. vm_compute. reflexivity. Qed.

Example append_compatible : bool_decide (sub_module a a_a) = true.
Proof. vm_compute. reflexivity. Qed.

Example append_conflict_distinct :
  variable_type a_b "N::q"%cpp_name = Some "N::@1*"%cpp_type.
Proof. vm_compute. reflexivity. Qed.

Example append_conflict : bool_decide (sub_module a a_b) = true.
Proof. vm_compute. reflexivity. Qed.

(** Prepending the colliding block renames [a]'s record to [N::@1], and gives
    [N::.a] the other definition. *)
Example prepend_conflict_renamed :
  variable_type b_a "N::p"%cpp_name = Some "N::@1*"%cpp_type.
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
