Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.syntax.templates.
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

template <typename T, typename U = bool>
struct ConcreteDefault {
  T first;
  U second;
};

template <typename T, typename U = T, typename V = U *>
struct PointerChain {
  T first;
  U second;
  V third;
};

template <typename T, int N = 0>
struct ValueDefault {
  T value;
};

template <typename T>
struct TemplateTemplateDefaultArg {
  T value;
};

template <template <typename> class TT = TemplateTemplateDefaultArg>
struct TemplateTemplateDefault {
};

template <int N>
struct ValueOuter {
  template <typename T, typename U = T>
  struct Inner {
    T first;
    U second;
  };
};

template <typename T, typename U = T>
struct ForwardDefault;

template <typename T, typename U = T>
union DefaultedUnion {
  T first;
  U second;
};

template <typename T, typename U = T>
using DefaultedTypeAlias = DefaultedPair<T, U>;

template <typename T, typename U = bool>
using ExplicitAlias = DefaultedPair<U, T>;

template <typename OuterT>
struct Outer {
  template <typename InnerT, typename InnerU = OuterT>
  struct Inner {
    InnerT first;
    InnerU second;
  };
};

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

Definition lookup_alias_template (n : name) : option (template type) :=
  translation_unit.maliases source !! n.

Definition alias_template_params (n : name) : option (list temp_param) :=
  match lookup_alias_template n with
  | Some t => Some t.(template_params)
  | None => None
  end.

Definition alias_template_value (n : name) : option type :=
  match lookup_alias_template n with
  | Some t => Some t.(template_value)
  | None => None
  end.

Definition template_template_default_alias_name : name :=
  Ninst (Nglobal (Nid "TemplateTemplateDefault")) [].

Example defaulted_pair_generated_alias_params :
  alias_template_params "DefaultedPair<$T>"%cpp_name = Some [Ptype "T"].
Proof. vm_compute. reflexivity. Qed.

Example defaulted_pair_generated_alias_target :
  alias_template_value "DefaultedPair<$T>"%cpp_name =
  Some "DefaultedPair<$T, $T>"%cpp_type.
Proof. vm_compute. reflexivity. Qed.

Example defaulted_pair_does_not_generate_full_arity_alias :
  lookup_alias_template "DefaultedPair<$T, $U>"%cpp_name = None.
Proof. vm_compute. reflexivity. Qed.

Example defaulted_chain_one_arg_generated_alias_params :
  alias_template_params "DefaultedChain<$T>"%cpp_name = Some [Ptype "T"].
Proof. vm_compute. reflexivity. Qed.

Example defaulted_chain_one_arg_generated_alias_target :
  alias_template_value "DefaultedChain<$T>"%cpp_name =
  Some "DefaultedChain<$T, $T, $T>"%cpp_type.
Proof. vm_compute. reflexivity. Qed.

Example defaulted_chain_two_arg_generated_alias_params :
  alias_template_params "DefaultedChain<$T, $U>"%cpp_name =
  Some [Ptype "T"; Ptype "U"].
Proof. vm_compute. reflexivity. Qed.

Example defaulted_chain_two_arg_generated_alias_target :
  alias_template_value "DefaultedChain<$T, $U>"%cpp_name =
  Some "DefaultedChain<$T, $U, $U>"%cpp_type.
Proof. vm_compute. reflexivity. Qed.

Example concrete_default_generated_alias_target :
  alias_template_value "ConcreteDefault<$T>"%cpp_name =
  Some "ConcreteDefault<$T, bool>"%cpp_type.
Proof. vm_compute. reflexivity. Qed.

Example pointer_chain_generated_alias_target_substitutes_inside_pointer :
  alias_template_value "PointerChain<$T>"%cpp_name =
  Some "PointerChain<$T, $T, $T*>"%cpp_type.
Proof. vm_compute. reflexivity. Qed.

Example value_default_does_not_generate_unsupported_alias :
  lookup_alias_template "ValueDefault<$T>"%cpp_name = None.
Proof. vm_compute. reflexivity. Qed.

Example template_template_default_does_not_generate_unsupported_alias :
  lookup_alias_template template_template_default_alias_name = None.
Proof. vm_compute. reflexivity. Qed.

Example value_outer_inner_does_not_generate_unsupported_enclosing_alias :
  lookup_alias_template "ValueOuter<`N>::Inner<$T>"%cpp_name = None.
Proof. vm_compute. reflexivity. Qed.

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

Example concrete_default_resolves_through_generated_alias :
  RESOLVE_TYPE "ConcreteDefault<int>" "ConcreteDefault<int, bool>".
Proof. vm_compute. reflexivity. Qed.

Example concrete_default_template_type_resolves_through_generated_alias :
  RESOLVE_TYPE "ConcreteDefault<$T>" "ConcreteDefault<$T, bool>".
Proof. vm_compute. reflexivity. Qed.

Example pointer_chain_resolves_compound_default_substitution :
  RESOLVE_TYPE "PointerChain<int>" "PointerChain<int, int, int*>".
Proof. vm_compute. reflexivity. Qed.

Example pointer_chain_template_type_resolves_compound_default_substitution :
  RESOLVE_TYPE "PointerChain<$T>" "PointerChain<$T, $T, $T*>".
Proof. vm_compute. reflexivity. Qed.

Example forward_default_resolves_from_declaration :
  RESOLVE_TYPE "ForwardDefault<int>" "ForwardDefault<int, int>".
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

Example explicit_alias_generated_alias_target_preserves_explicit_alias :
  alias_template_value "ExplicitAlias<$T>"%cpp_name =
  Some "ExplicitAlias<$T, bool>"%cpp_type.
Proof. vm_compute. reflexivity. Qed.

Example nested_default_generated_alias_params_include_outer_param :
  alias_template_params "Outer<$OuterT>::Inner<$InnerT>"%cpp_name =
  Some [Ptype "OuterT"; Ptype "InnerT"].
Proof. vm_compute. reflexivity. Qed.

Example nested_default_generated_alias_target_uses_outer_param :
  alias_template_value "Outer<$OuterT>::Inner<$InnerT>"%cpp_name =
  Some "Outer<$OuterT>::Inner<$InnerT, $OuterT>"%cpp_type.
Proof. vm_compute. reflexivity. Qed.

Example nested_default_resolves_through_generated_alias :
  RESOLVE_TYPE "Outer<int>::Inner<bool>"
               "Outer<int>::Inner<bool, int>".
Proof. vm_compute. reflexivity. Qed.

Example nested_default_template_type_resolves_through_generated_alias :
  RESOLVE_TYPE "Outer<$T>::Inner<$U>"
               "Outer<$T>::Inner<$U, $T>".
Proof. vm_compute. reflexivity. Qed.

Example scoped_default_resolves_through_generated_alias :
  RESOLVE_TYPE "DefaultNS::ScopedDefault<int>"
               "DefaultNS::ScopedDefault<int, int>".
Proof. vm_compute. reflexivity. Qed.

Example scoped_default_generated_alias_target :
  alias_template_value "DefaultNS::ScopedDefault<$T>"%cpp_name =
  Some "DefaultNS::ScopedDefault<$T, $T>"%cpp_type.
Proof. vm_compute. reflexivity. Qed.

Example scoped_default_template_type_resolves_through_generated_alias :
  RESOLVE_TYPE "DefaultNS::ScopedDefault<$T>"
               "DefaultNS::ScopedDefault<$T, $T>".
Proof. vm_compute. reflexivity. Qed.
