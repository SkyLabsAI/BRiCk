Require Import skylabs.lang.cpp.syntax.source_location.
Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.mparser.
Require Import fixture_20_cpp_locations.

#[local] Open Scope pstring_scope.

Definition decomposition_root : decl_root :=
  DRMsymbol
    (Ninst
      (Nglobal
        (core.Nfunction function_qualifiers.N "dependent_decomposition"
          [Tparam "T"]))
      [Atype (Tparam "T")]).

Definition lambda_root : decl_root :=
  DRMsymbol
    (Ninst
      (Nglobal
        (core.Nfunction function_qualifiers.N "dependent_lambda"
          [Tparam "T"]))
      [Atype (Tparam "T")]).

Definition classes (result : lookup_error + list source_origin)
    : list origin_kind :=
  match result with
  | inr origins => List.map origin_class origins
  | inl _ => []
  end.

Example dependent_binding_is_explicit :
    classes
      (skylabs.lang.cpp.syntax.source_location.lookup source_locations
        decomposition_root [1; 0; 2; 0; 0; 0; 1]) =
      [ExplicitOrigin].
Proof. vm_compute. reflexivity. Qed.

Example deferred_initializer_is_synthesized :
    classes
      (skylabs.lang.cpp.syntax.source_location.lookup source_locations
        decomposition_root [1; 0; 2; 0; 0; 0; 1; 1]) =
      [Cpp2vSynthesizedOrigin].
Proof. vm_compute. reflexivity. Qed.

Example deferred_initializer_type_is_inherited :
    classes
      (skylabs.lang.cpp.syntax.source_location.lookup source_locations
        decomposition_root [1; 0; 2; 0; 0; 0; 1; 1; 0]) =
      [InheritedOrigin].
Proof. vm_compute. reflexivity. Qed.

Example lambda_callee_reduction_retains_provenance :
    classes
      (skylabs.lang.cpp.syntax.source_location.lookup source_locations
        lambda_root [1; 0; 2; 0; 0; 0; 0]) =
      [Cpp2vSynthesizedOrigin; ClangTransformedOrigin].
Proof. vm_compute. reflexivity. Qed.
