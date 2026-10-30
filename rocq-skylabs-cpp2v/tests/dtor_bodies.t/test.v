From stdpp Require Import fin_maps.
Require Import skylabs.lang.cpp.syntax skylabs.lang.cpp.semantics.

Require test.inc_hpp.
Require test.inc_noelab_hpp.
Require test.src_cpp.

#[local] Ltac check := vm_compute; reflexivity.

(** The bodies of all destructors of a translation unit. *)
Definition dtor_bodies (tu : translation_unit) : list (obj_name * option (OrDefault Stmt)) :=
  List.flat_map (fun '(n, o) =>
    match o with
    | Odestructor d => [(n, d.(d_body))]
    | _ => []
    end) (map_to_list tu.(symbols)).

Eval vm_compute in dtor_bodies inc_hpp.source.
Eval vm_compute in dtor_bodies inc_noelab_hpp.source.
Eval vm_compute in dtor_bodies src_cpp.source.

(** [sub_module] relates the unelaborated header's [Defaulted] destructors to
    the source file's [CompilerProvided] ones. *)
Example _inc_in_src : bool_decide (sub_module inc_hpp.source src_cpp.source) = true :=
  ltac:(check).
Example _inc_noelab_in_src :
  bool_decide (sub_module inc_noelab_hpp.source src_cpp.source) = true :=
  ltac:(check).

(** Every [CompilerProvided] destructor body is empty: clang's
    [Sema::DefineImplicitDestructor] sets the body to an empty [CompoundStmt]
    and leaves member and base destruction to code generation. [wp_dtor] destroys
    members and bases after the body in every case, so an empty body behaves
    like [Defaulted]; [code_at_ok] relies on this when a [Defaulted]
    destructor is weakened to a [CompilerProvided] one. *)
Definition compiler_provided_empty (tu : translation_unit) : bool :=
  forallb (fun '(_, b) =>
    match b with
    | Some (CompilerProvided s) => bool_decide (s = Sseq [])
    | _ => true
    end) (dtor_bodies tu).

Example _src_dtors_empty : compiler_provided_empty src_cpp.source = true :=
  ltac:(check).

Goal True.
  idtac "Success!".
  exact I.
Qed.
