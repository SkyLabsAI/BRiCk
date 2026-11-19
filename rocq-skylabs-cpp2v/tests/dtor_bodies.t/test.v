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
    the source file's, which cpp2v also prints as [Defaulted]. *)
Example _inc_in_src : bool_decide (sub_module inc_hpp.source src_cpp.source) = true :=
  ltac:(check).
Example _inc_noelab_in_src :
  bool_decide (sub_module inc_noelab_hpp.source src_cpp.source) = true :=
  ltac:(check).

(** No destructor is [CompilerProvided]: clang's
    [Sema::DefineImplicitDestructor] gives implicit and defaulted destructors
    an empty [CompoundStmt], and cpp2v prints those as [Defaulted] (and any
    other body as unsupported). *)
Definition no_compiler_provided (tu : translation_unit) : bool :=
  forallb (fun '(_, b) =>
    match b with
    | Some (CompilerProvided _) => false
    | _ => true
    end) (dtor_bodies tu).

Example _inc_no_compiler_provided : no_compiler_provided inc_hpp.source = true :=
  ltac:(check).
Example _src_no_compiler_provided : no_compiler_provided src_cpp.source = true :=
  ltac:(check).

Goal True.
Proof.
  idtac "Success!".
  exact I.
Qed.
