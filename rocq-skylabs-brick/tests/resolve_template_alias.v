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

template <typename T, typename U = T, typename V = U[2]>
struct ArrayDefaultChain {
  T first;
  U second;
  V third;
};

template <typename T, typename U = T, typename V = U ( * )(U)>
struct FunctionPointerDefaultChain {
  T first;
  U second;
  V third;
};

struct MemberHost {
};

template <typename T, typename U = T, typename V = U MemberHost::*>
struct MemberPointerDefaultChain {
  T first;
  U second;
  V third;
};

template <typename T, typename U = T, typename V = U &>
struct ReferenceDefaultChain {
  T first;
  U second;
  V third;
};

template <typename T, typename U = T, typename V = U &&>
struct RvalueReferenceDefaultChain {
  T first;
  U second;
  V third;
};

template <typename T, typename U = T, typename V = const U>
struct QualifiedDefaultChain {
  T first;
  U second;
  V third;
};

template <typename T, typename U = T, typename V = const U *>
struct QualifiedPointerDefaultChain {
  T first;
  U second;
  V third;
};

template <typename T, typename U = T, typename V = U (*)(const U *, U &)>
struct FunctionMixedDefaultChain {
  T first;
  U second;
  V third;
};

template <typename T, typename U = T, typename V = DefaultedPair<U *, const U &>>
struct SpecializationNestedDefaultChain {
  T first;
  U second;
  V third;
};

template <typename T, int N = 0>
struct ValueDefault {
  T value;
};

template <typename T, int N = 4>
struct ValueLiteralDefault {
  T value;
};

template <typename T, int N, int M = N>
struct ValueParamDefault {
  T value;
};

template <typename T, int N, int M = N + 1>
struct ValueExpressionDefault {
  T value;
};

template <typename T, unsigned long N = sizeof(T)>
struct SizeofTypeDefault {
  T value;
};

template <int N, typename T = int>
struct ValueThenTypeDefault {
  T value;
};

template <int N = 2, int M = N, typename T = int>
struct ValueLiteralPriorTypeMix {
  T value;
};

template <typename T, int N = 4>
using ValueDefaultTypeAlias = DefaultedPair<T, T>;

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

template <typename T, typename U = T, typename V = DefaultedTypeAlias<U>>
struct AliasDefaultChain {
  T first;
  U second;
  V third;
};

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

Definition same_template_base :=
  translation_unit.template_alias.same_template_base.

Definition defaulted_function_pointer_type : type :=
  Tptr (core.Tfunction (FunctionType (Tparam "T") [Tparam "T"])).

Definition defaulted_member_pointer_type : type :=
  Tmember_pointer (Tnamed "MemberHost"%cpp_name) (Tparam "T").

Definition function_pointer_default_chain_one_arg : type :=
  Tnamed (Ninst (Nglobal (Nid "FunctionPointerDefaultChain"))
    [Atype (Tparam "T");
     Atype (Tparam "T");
     Atype defaulted_function_pointer_type]).

Definition member_pointer_default_chain_one_arg : type :=
  Tnamed (Ninst (Nglobal (Nid "MemberPointerDefaultChain"))
    [Atype (Tparam "T");
     Atype (Tparam "T");
     Atype defaulted_member_pointer_type]).

Definition reference_default_chain_one_arg : type :=
  Tnamed (Ninst (Nglobal (Nid "ReferenceDefaultChain"))
    [Atype (Tparam "T");
     Atype (Tparam "T");
     Atype (Tref (Tparam "T"))]).

Definition rvalue_reference_default_chain_one_arg : type :=
  Tnamed (Ninst (Nglobal (Nid "RvalueReferenceDefaultChain"))
    [Atype (Tparam "T");
     Atype (Tparam "T");
     Atype (Trv_ref (Tparam "T"))]).

Definition qualified_default_chain_one_arg : type :=
  Tnamed (Ninst (Nglobal (Nid "QualifiedDefaultChain"))
    [Atype (Tparam "T");
     Atype (Tparam "T");
     Atype (Tconst (Tparam "T"))]).

Definition qualified_pointer_default_chain_one_arg : type :=
  Tnamed (Ninst (Nglobal (Nid "QualifiedPointerDefaultChain"))
    [Atype (Tparam "T");
     Atype (Tparam "T");
     Atype (Tptr (Tconst (Tparam "T")))]).

Definition function_mixed_default_type : type :=
  Tptr (core.Tfunction
    (FunctionType (Tparam "T")
      [Tptr (Tconst (Tparam "T")); Tref (Tparam "T")])).

Definition function_mixed_default_chain_one_arg : type :=
  Tnamed (Ninst (Nglobal (Nid "FunctionMixedDefaultChain"))
    [Atype (Tparam "T");
     Atype (Tparam "T");
     Atype function_mixed_default_type]).

Definition specialization_nested_default_type : type :=
  Tnamed (Ninst (Nglobal (Nid "DefaultedPair"))
    [Atype (Tptr (Tparam "T"));
     Atype (Tref (Tconst (Tparam "T")))]).

Definition specialization_nested_default_chain_one_arg : type :=
  Tnamed (Ninst (Nglobal (Nid "SpecializationNestedDefaultChain"))
    [Atype (Tparam "T");
     Atype (Tparam "T");
     Atype specialization_nested_default_type]).

Definition value_default_one_arg_params : list temp_param :=
  [Ptype "T"].

Definition value_default_one_arg_target : type :=
  Tnamed "ValueDefault<$T, 0>"%cpp_name.

Definition value_literal_default_one_arg_params : list temp_param :=
  [Ptype "T"].

Definition value_literal_default_one_arg_target : type :=
  Tnamed "ValueLiteralDefault<$T, 4>"%cpp_name.

Definition value_param_default_two_arg_params : list temp_param :=
  [Ptype "T"; Pvalue "N" Tint].

Definition value_param_default_two_arg_target : type :=
  Tnamed "ValueParamDefault<$T, `N, `N>"%cpp_name.

Definition value_then_type_default_one_arg_params : list temp_param :=
  [Pvalue "N" Tint].

Definition value_then_type_default_one_arg_target : type :=
  Tnamed "ValueThenTypeDefault<`N, int>"%cpp_name.

Definition value_default_type_alias_one_arg_params : list temp_param :=
  [Ptype "T"].

Definition value_default_type_alias_one_arg_target : type :=
  Tnamed "ValueDefaultTypeAlias<$T, 4>"%cpp_name.

Definition value_literal_prior_type_mix_zero_arg_name : name :=
  Ninst (Nglobal (Nid "ValueLiteralPriorTypeMix")) [].

Definition value_literal_prior_type_mix_zero_arg_target : type :=
  Tnamed "ValueLiteralPriorTypeMix<2, 2, int>"%cpp_name.

Definition value_literal_prior_type_mix_one_arg_params : list temp_param :=
  [Pvalue "N" Tint].

Definition value_literal_prior_type_mix_one_arg_target : type :=
  Tnamed "ValueLiteralPriorTypeMix<`N, `N, int>"%cpp_name.

Definition value_literal_prior_type_mix_two_arg_params : list temp_param :=
  [Pvalue "N" Tint; Pvalue "M" Tint].

Definition value_literal_prior_type_mix_two_arg_target : type :=
  Tnamed "ValueLiteralPriorTypeMix<`N, `M, int>"%cpp_name.

Definition value_expression_default_two_arg_target : type :=
  Tnamed (Ninst (Nglobal (Nid "ValueExpressionDefault"))
    [Atype (Tparam "T");
     Avalue (Eparam "N");
     Avalue (Ebinop Badd (Eparam "N") (Eint 1 Tint) Tint)]).

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

Example array_default_chain_generated_alias_target_substitutes_inside_array :
  alias_template_value "ArrayDefaultChain<$T>"%cpp_name =
  Some "ArrayDefaultChain<$T, $T, $T[2]>"%cpp_type.
Proof. vm_compute. reflexivity. Qed.

Example function_pointer_default_chain_generated_alias_target_substitutes_inside_function :
  alias_template_value "FunctionPointerDefaultChain<$T>"%cpp_name =
  Some function_pointer_default_chain_one_arg.
Proof. vm_compute. reflexivity. Qed.

Example member_pointer_default_chain_generated_alias_target_substitutes_inside_member_pointer :
  alias_template_value "MemberPointerDefaultChain<$T>"%cpp_name =
  Some member_pointer_default_chain_one_arg.
Proof. vm_compute. reflexivity. Qed.

Example reference_default_chain_generated_alias_target_substitutes_inside_reference :
  alias_template_value "ReferenceDefaultChain<$T>"%cpp_name =
  Some reference_default_chain_one_arg.
Proof. vm_compute. reflexivity. Qed.

Example rvalue_reference_default_chain_generated_alias_target_substitutes_inside_reference :
  alias_template_value "RvalueReferenceDefaultChain<$T>"%cpp_name =
  Some rvalue_reference_default_chain_one_arg.
Proof. vm_compute. reflexivity. Qed.

Example qualified_default_chain_generated_alias_target_substitutes_under_cv :
  alias_template_value "QualifiedDefaultChain<$T>"%cpp_name =
  Some qualified_default_chain_one_arg.
Proof. vm_compute. reflexivity. Qed.

Example qualified_pointer_default_chain_generated_alias_target_substitutes_under_pointer_and_cv :
  alias_template_value "QualifiedPointerDefaultChain<$T>"%cpp_name =
  Some qualified_pointer_default_chain_one_arg.
Proof. vm_compute. reflexivity. Qed.

Example function_mixed_default_chain_generated_alias_target_substitutes_inside_function_parts :
  alias_template_value "FunctionMixedDefaultChain<$T>"%cpp_name =
  Some function_mixed_default_chain_one_arg.
Proof. vm_compute. reflexivity. Qed.

Example specialization_nested_default_chain_generated_alias_target_substitutes_inside_template_args :
  alias_template_value "SpecializationNestedDefaultChain<$T>"%cpp_name =
  Some specialization_nested_default_chain_one_arg.
Proof. vm_compute. reflexivity. Qed.

Example alias_default_chain_generated_alias_target_expands_alias_default :
  alias_template_value "AliasDefaultChain<$T>"%cpp_name =
  Some "AliasDefaultChain<$T, $T, DefaultedPair<$T, $T>>"%cpp_type.
Proof. vm_compute. reflexivity. Qed.

Example alias_default_chain_two_arg_generated_alias_target_expands_alias_default :
  alias_template_value "AliasDefaultChain<$T, $U>"%cpp_name =
  Some "AliasDefaultChain<$T, $U, DefaultedPair<$U, $U>>"%cpp_type.
Proof. vm_compute. reflexivity. Qed.

Example value_default_generated_alias_params :
  alias_template_params "ValueDefault<$T>"%cpp_name =
  Some value_default_one_arg_params.
Proof. vm_compute. reflexivity. Qed.

Example value_default_generated_alias_target :
  alias_template_value "ValueDefault<$T>"%cpp_name =
  Some value_default_one_arg_target.
Proof. vm_compute. reflexivity. Qed.

Example value_literal_default_generated_alias_params :
  alias_template_params "ValueLiteralDefault<$T>"%cpp_name =
  Some value_literal_default_one_arg_params.
Proof. vm_compute. reflexivity. Qed.

Example value_literal_default_generated_alias_target :
  alias_template_value "ValueLiteralDefault<$T>"%cpp_name =
  Some value_literal_default_one_arg_target.
Proof. vm_compute. reflexivity. Qed.

Example value_param_default_generated_alias_params :
  alias_template_params "ValueParamDefault<$T, `N>"%cpp_name =
  Some value_param_default_two_arg_params.
Proof. vm_compute. reflexivity. Qed.

Example value_param_default_generated_alias_target :
  alias_template_value "ValueParamDefault<$T, `N>"%cpp_name =
  Some value_param_default_two_arg_target.
Proof. vm_compute. reflexivity. Qed.

Example value_expression_default_does_not_generate_unsupported_alias :
  lookup_alias_template "ValueExpressionDefault<$T, `N>"%cpp_name = None.
Proof. vm_compute. reflexivity. Qed.

Example sizeof_type_default_does_not_generate_unsupported_alias :
  lookup_alias_template "SizeofTypeDefault<$T>"%cpp_name = None.
Proof. vm_compute. reflexivity. Qed.

Example value_then_type_default_generated_alias_params :
  alias_template_params "ValueThenTypeDefault<`N>"%cpp_name =
  Some value_then_type_default_one_arg_params.
Proof. vm_compute. reflexivity. Qed.

Example value_then_type_default_generated_alias_target :
  alias_template_value "ValueThenTypeDefault<`N>"%cpp_name =
  Some value_then_type_default_one_arg_target.
Proof. vm_compute. reflexivity. Qed.

Example value_default_type_alias_generated_alias_params :
  alias_template_params "ValueDefaultTypeAlias<$T>"%cpp_name =
  Some value_default_type_alias_one_arg_params.
Proof. vm_compute. reflexivity. Qed.

Example value_default_type_alias_generated_alias_target :
  alias_template_value "ValueDefaultTypeAlias<$T>"%cpp_name =
  Some value_default_type_alias_one_arg_target.
Proof. vm_compute. reflexivity. Qed.

Example value_literal_prior_type_mix_zero_arg_generated_alias_params :
  alias_template_params value_literal_prior_type_mix_zero_arg_name =
  Some [].
Proof. vm_compute. reflexivity. Qed.

Example value_literal_prior_type_mix_zero_arg_generated_alias_target :
  alias_template_value value_literal_prior_type_mix_zero_arg_name =
  Some value_literal_prior_type_mix_zero_arg_target.
Proof. vm_compute. reflexivity. Qed.

Example value_literal_prior_type_mix_one_arg_generated_alias_params :
  alias_template_params "ValueLiteralPriorTypeMix<`N>"%cpp_name =
  Some value_literal_prior_type_mix_one_arg_params.
Proof. vm_compute. reflexivity. Qed.

Example value_literal_prior_type_mix_one_arg_generated_alias_target :
  alias_template_value "ValueLiteralPriorTypeMix<`N>"%cpp_name =
  Some value_literal_prior_type_mix_one_arg_target.
Proof. vm_compute. reflexivity. Qed.

Example value_literal_prior_type_mix_two_arg_generated_alias_params :
  alias_template_params "ValueLiteralPriorTypeMix<`N, `M>"%cpp_name =
  Some value_literal_prior_type_mix_two_arg_params.
Proof. vm_compute. reflexivity. Qed.

Example value_literal_prior_type_mix_two_arg_generated_alias_target :
  alias_template_value "ValueLiteralPriorTypeMix<`N, `M>"%cpp_name =
  Some value_literal_prior_type_mix_two_arg_target.
Proof. vm_compute. reflexivity. Qed.

Fail Definition value_expression_default_future_alias_target :
  alias_template_value "ValueExpressionDefault<$T, `N>"%cpp_name =
  Some value_expression_default_two_arg_target := eq_refl.

Example template_template_default_does_not_generate_unsupported_alias :
  lookup_alias_template template_template_default_alias_name = None.
Proof. vm_compute. reflexivity. Qed.

Example value_outer_inner_generated_alias_params_include_outer_value_param :
  alias_template_params "ValueOuter<`N>::Inner<$T>"%cpp_name =
  Some [Pvalue "N" Tint; Ptype "T"].
Proof. vm_compute. reflexivity. Qed.

Example value_outer_inner_generated_alias_target :
  alias_template_value "ValueOuter<`N>::Inner<$T>"%cpp_name =
  Some "ValueOuter<`N>::Inner<$T, $T>"%cpp_type.
Proof. vm_compute. reflexivity. Qed.

Example same_template_base_nested_positive :
  same_template_base "Outer<int>::Inner<bool>"%cpp_name
                     "Outer<$T>::Inner<$U>"%cpp_name =
  Some [Atype Tint; Atype Tbool].
Proof. vm_compute. reflexivity. Qed.

Example same_template_base_rejects_different_outer_arity :
  same_template_base
    (Ninst
      (Nscoped
        (Ninst (Nglobal (Nid "Outer")) [Atype Tint; Atype Tbool])
        (Nid "Inner"))
      [])
    "Outer<$T>::Inner<$U>"%cpp_name = None.
Proof. vm_compute. reflexivity. Qed.

Example same_template_base_rejects_different_leaf_name :
  same_template_base "Outer<int>::Other<bool>"%cpp_name
                     "Outer<$T>::Inner<$U>"%cpp_name = None.
Proof. vm_compute. reflexivity. Qed.

Example same_template_base_collects_value_arguments :
  same_template_base "ValueParamDefault<int, 3>"%cpp_name
                     "ValueParamDefault<$T, `N>"%cpp_name =
  Some [Atype Tint; Avalue (Eint 3 Tint)].
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

Example array_default_chain_template_type_resolves_compound_default_substitution :
  RESOLVE_TYPE "ArrayDefaultChain<$T>" "ArrayDefaultChain<$T, $T, $T[2]>".
Proof. vm_compute. reflexivity. Qed.

Example function_pointer_default_chain_template_type_resolves_compound_default_substitution :
  trace.runO (dealias.resolveTN source "FunctionPointerDefaultChain<$T>"%cpp_name) =
  Some function_pointer_default_chain_one_arg.
Proof. vm_compute. reflexivity. Qed.

Example member_pointer_default_chain_template_type_resolves_compound_default_substitution :
  trace.runO (dealias.resolveTN source "MemberPointerDefaultChain<$T>"%cpp_name) =
  Some member_pointer_default_chain_one_arg.
Proof. vm_compute. reflexivity. Qed.

Example reference_default_chain_template_type_resolves_compound_default_substitution :
  trace.runO (dealias.resolveTN source "ReferenceDefaultChain<$T>"%cpp_name) =
  Some reference_default_chain_one_arg.
Proof. vm_compute. reflexivity. Qed.

Example rvalue_reference_default_chain_template_type_resolves_compound_default_substitution :
  trace.runO (dealias.resolveTN source "RvalueReferenceDefaultChain<$T>"%cpp_name) =
  Some rvalue_reference_default_chain_one_arg.
Proof. vm_compute. reflexivity. Qed.

Example qualified_default_chain_template_type_resolves_compound_default_substitution :
  trace.runO (dealias.resolveTN source "QualifiedDefaultChain<$T>"%cpp_name) =
  Some qualified_default_chain_one_arg.
Proof. vm_compute. reflexivity. Qed.

Example qualified_pointer_default_chain_template_type_resolves_compound_default_substitution :
  trace.runO (dealias.resolveTN source "QualifiedPointerDefaultChain<$T>"%cpp_name) =
  Some qualified_pointer_default_chain_one_arg.
Proof. vm_compute. reflexivity. Qed.

Example function_mixed_default_chain_template_type_resolves_compound_default_substitution :
  trace.runO (dealias.resolveTN source "FunctionMixedDefaultChain<$T>"%cpp_name) =
  Some function_mixed_default_chain_one_arg.
Proof. vm_compute. reflexivity. Qed.

Example specialization_nested_default_chain_template_type_resolves_compound_default_substitution :
  trace.runO (dealias.resolveTN source "SpecializationNestedDefaultChain<$T>"%cpp_name) =
  Some specialization_nested_default_chain_one_arg.
Proof. vm_compute. reflexivity. Qed.

Example alias_default_chain_resolves_alias_default :
  RESOLVE_TYPE "AliasDefaultChain<int>"
               "AliasDefaultChain<int, int, DefaultedPair<int, int>>".
Proof. vm_compute. reflexivity. Qed.

Example alias_default_chain_template_type_resolves_alias_default :
  RESOLVE_TYPE "AliasDefaultChain<$T>"
               "AliasDefaultChain<$T, $T, DefaultedPair<$T, $T>>".
Proof. vm_compute. reflexivity. Qed.

Example alias_default_chain_two_arg_template_type_resolves_alias_default :
  RESOLVE_TYPE "AliasDefaultChain<$T, $U>"
               "AliasDefaultChain<$T, $U, DefaultedPair<$U, $U>>".
Proof. vm_compute. reflexivity. Qed.

Example value_default_resolves_literal_non_type_default :
  trace.runO (dealias.resolveTN source "ValueDefault<$T>"%cpp_name) =
  Some value_default_one_arg_target.
Proof. vm_compute. reflexivity. Qed.

Example value_literal_default_resolves_literal_non_type_default :
  trace.runO (dealias.resolveTN source "ValueLiteralDefault<$T>"%cpp_name) =
  Some value_literal_default_one_arg_target.
Proof. vm_compute. reflexivity. Qed.

Example value_param_default_resolves_prior_parameter_default :
  trace.runO (dealias.resolveTN source "ValueParamDefault<$T, `N>"%cpp_name) =
  Some value_param_default_two_arg_target.
Proof. vm_compute. reflexivity. Qed.

Example value_then_type_default_resolves_mixed_value_and_type_default :
  trace.runO (dealias.resolveTN source "ValueThenTypeDefault<`N>"%cpp_name) =
  Some value_then_type_default_one_arg_target.
Proof. vm_compute. reflexivity. Qed.

Example value_default_type_alias_resolves_literal_default_via_explicit_body :
  RESOLVE_TYPE "ValueDefaultTypeAlias<$T>" "DefaultedPair<$T, $T>".
Proof. vm_compute. reflexivity. Qed.

Example value_literal_prior_type_mix_resolves_recursive_defaults :
  trace.runO (dealias.resolveTN source value_literal_prior_type_mix_zero_arg_name) =
  Some value_literal_prior_type_mix_zero_arg_target.
Proof. vm_compute. reflexivity. Qed.

Example value_literal_prior_type_mix_one_arg_resolves_prior_parameter_default :
  trace.runO (dealias.resolveTN source "ValueLiteralPriorTypeMix<`N>"%cpp_name) =
  Some value_literal_prior_type_mix_one_arg_target.
Proof. vm_compute. reflexivity. Qed.

Example value_literal_prior_type_mix_two_arg_resolves_type_default :
  trace.runO (dealias.resolveTN source "ValueLiteralPriorTypeMix<`N, `M>"%cpp_name) =
  Some value_literal_prior_type_mix_two_arg_target.
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
