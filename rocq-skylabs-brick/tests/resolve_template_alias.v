Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.syntax.dealias.
Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.

#[with_templates]
cpp.prog source flags "-std=c++20" prog cpp:{{
template <typename T, typename U = T>
struct DefaultedPair {
  T first;
  U second;
};

template <typename T, typename U = T, typename V = U>
struct DefaultedChain {
  T first;
  U second;
  V third;
};

template <typename T, typename U = T>
union DefaultedUnion {
  T first;
  U second;
};

template <typename T, typename U = T>
using DefaultedTypeAlias = DefaultedPair<T, U>;

template <typename T, typename U = bool>
using ExplicitAlias = DefaultedPair<U, T>;

namespace DefaultNS {
  template <typename T, typename U = T>
  struct ScopedDefault {
    T first;
    U second;
  };
}
}}.

Notation RESOLVE_TYPE input output :=
  (trace.runO (dealias.resolveTN source input%cpp_name) = Some output%cpp_type)
  (only parsing).

Example defaulted_pair_resolves_through_generated_alias :
  RESOLVE_TYPE "DefaultedPair<int>" "DefaultedPair<int, int>".
Proof. vm_compute. reflexivity. Qed.

Example defaulted_pair_template_type_resolves_through_generated_alias :
  RESOLVE_TYPE "DefaultedPair<$T>" "DefaultedPair<$T, $T>".
Proof. vm_compute. reflexivity. Qed.

Example defaulted_pair_preserves_explicit_argument :
  RESOLVE_TYPE "DefaultedPair<int, bool>" "DefaultedPair<int, bool>".
Proof. vm_compute. reflexivity. Qed.

Example defaulted_chain_one_arg_resolves_through_generated_alias :
  RESOLVE_TYPE "DefaultedChain<int>" "DefaultedChain<int, int, int>".
Proof. vm_compute. reflexivity. Qed.

Example defaulted_chain_one_arg_template_type_resolves_through_generated_alias :
  RESOLVE_TYPE "DefaultedChain<$T>" "DefaultedChain<$T, $T, $T>".
Proof. vm_compute. reflexivity. Qed.

Example defaulted_chain_two_args_resolve_through_generated_alias :
  RESOLVE_TYPE "DefaultedChain<int, bool>" "DefaultedChain<int, bool, bool>".
Proof. vm_compute. reflexivity. Qed.

Example defaulted_chain_two_arg_template_type_resolves_through_generated_alias :
  RESOLVE_TYPE "DefaultedChain<$T, $U>" "DefaultedChain<$T, $U, $U>".
Proof. vm_compute. reflexivity. Qed.

Example defaulted_union_resolves_through_generated_alias :
  RESOLVE_TYPE "DefaultedUnion<int>" "DefaultedUnion<int, int>".
Proof. vm_compute. reflexivity. Qed.

Example defaulted_union_template_type_resolves_through_generated_alias :
  RESOLVE_TYPE "DefaultedUnion<$T>" "DefaultedUnion<$T, $T>".
Proof. vm_compute. reflexivity. Qed.

Example defaulted_type_alias_resolves_through_generated_alias :
  RESOLVE_TYPE "DefaultedTypeAlias<int>" "DefaultedPair<int, int>".
Proof. vm_compute. reflexivity. Qed.

Example defaulted_type_alias_template_type_resolves_through_generated_alias :
  RESOLVE_TYPE "DefaultedTypeAlias<$T>" "DefaultedPair<$T, $T>".
Proof. vm_compute. reflexivity. Qed.

Example explicit_alias_preserves_its_body_over_default_target :
  RESOLVE_TYPE "ExplicitAlias<int, char>" "DefaultedPair<char, int>".
Proof. vm_compute. reflexivity. Qed.

Example explicit_alias_generated_default_resolves_via_explicit_body :
  RESOLVE_TYPE "ExplicitAlias<int>" "DefaultedPair<bool, int>".
Proof. vm_compute. reflexivity. Qed.

Example explicit_alias_template_type_resolves_via_explicit_body :
  RESOLVE_TYPE "ExplicitAlias<$T>" "DefaultedPair<bool, $T>".
Proof. vm_compute. reflexivity. Qed.

Example scoped_default_resolves_through_generated_alias :
  RESOLVE_TYPE "DefaultNS::ScopedDefault<int>"
               "DefaultNS::ScopedDefault<int, int>".
Proof. vm_compute. reflexivity. Qed.

Example scoped_default_template_type_resolves_through_generated_alias :
  RESOLVE_TYPE "DefaultNS::ScopedDefault<$T>"
               "DefaultNS::ScopedDefault<$T, $T>".
Proof. vm_compute. reflexivity. Qed.
