Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.syntax.templates.
Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.syntax.dealias.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.

#[with_templates]
cpp.prog source flags "-std=c++20" prog cpp:{{
struct T {
  int tag;
};

int N = 100;
int value = 200;

template <typename T>
T type_shadow(T value) {
  return value;
}

template <int N>
int value_shadow() {
  return N;
}

template <typename Outer>
struct Nested {
  Outer field;

  template <typename Inner>
  Inner method(Outer outer, Inner inner) {
    return inner;
  }
};

template <typename T, int N>
struct Mixed {
  T slots[N];
};

template <typename T>
using Alias = T *;

template <typename T>
using ConstAlias = const T *;

template <typename T>
using RefAlias = T &;

template <typename T>
using AliasChain = Alias<T>;

template <typename T>
using NestedPtrAlias = Alias<Alias<T>>;

template <int N>
using ValueAlias = int;

template <int N>
using ValueArrayAlias = int[N];

template <template <typename T> class TemplateParam, typename T>
using ApplyAlias = TemplateParam<T>;

struct AliasHolder {
  template <typename T>
  using MemberAlias = Alias<T>;
};

namespace AliasNS {
  template <typename T>
  using ScopedAlias = Alias<T>;

  using ConcreteScopedPtr = ScopedAlias<int>;
}

using ConcreteAliasPtr = Alias<int>;
using ConcreteAliasChain = AliasChain<int>;
using ConcreteMemberPtr = AliasHolder::MemberAlias<int>;
using ConcreteNestedPtr = NestedPtrAlias<int>;

void takes_ptr(int *);
void takes_const_ptr(const int *);
void takes_ref(int &);
void takes_nested_ptr(int **);
void takes_value_alias(int);
void takes_value_array_alias(int (&)[3]);
void takes_apply_alias(int *);

template <typename T>
T templated_var = {};

template <template <typename T> class TemplateParam, typename T>
struct UsesTemplateTemplate {
  TemplateParam<T> value;
};

template <typename... Ts>
int variadic_count(Ts... values) {
  return sizeof...(values);
}

struct Agg {
  int a;
  int b;
};

template <Agg V>
int aggregate_value() {
  return V.a;
}

int use_all() {
  Nested<int> nested;
  return value_shadow<7>() + variadic_count(1, 2, 3) +
         aggregate_value<Agg{4, 5}>();
}
}}.

Definition lookup_symbol_template (n : name) : option (template ObjValue) :=
  translation_unit.msymbols source !! n.

Definition lookup_type_template (n : name) : option (template GlobDecl) :=
  translation_unit.mtypes source !! n.

Definition lookup_function_template (n : name) : option Func :=
  match lookup_symbol_template n with
  | Some t =>
    match t.(template_value) with
    | Ofunction f => Some f
    | _ => None
    end
  | None => None
  end.

Definition lookup_method_template (n : name) : option Method :=
  match lookup_symbol_template n with
  | Some t =>
    match t.(template_value) with
    | Omethod m => Some m
    | _ => None
    end
  | None => None
  end.

Definition lookup_function_template_body (n : name) : option Stmt :=
  match lookup_function_template n with
  | Some f =>
    match f.(f_body) with
    | Some (Impl s) => Some s
    | _ => None
    end
  | None => None
  end.

Definition lookup_method_template_body (n : name) : option Stmt :=
  match lookup_method_template n with
  | Some m =>
    match m.(m_body) with
    | Some (UserDefined s) => Some s
    | _ => None
    end
  | None => None
  end.

Definition symbol_template_params (n : name) : option (list temp_param) :=
  match lookup_symbol_template n with
  | Some t => Some t.(template_params)
  | None => None
  end.

Definition type_template_params (n : name) : option (list temp_param) :=
  match lookup_type_template n with
  | Some t => Some t.(template_params)
  | None => None
  end.

Definition alias_template_params (n : name) : option (list temp_param) :=
  match translation_unit.maliases source !! n with
  | Some t => Some t.(template_params)
  | None => None
  end.

Notation RESOLVE_VALUE input output :=
  (trace.runO (dealias.resolveValue source input%cpp_name) = Some output%cpp_name)
  (only parsing).

Definition type_shadow_name : name :=
  "type_shadow<$T>($T)"%cpp_name.

Definition value_shadow_name : name :=
  "value_shadow<`N>()"%cpp_name.

Definition nested_type_name : name :=
  "Nested<$Outer>"%cpp_name.

Definition nested_method_name : name :=
  "Nested<$Outer>::method<$Inner>($Outer, $Inner)"%cpp_name.

Definition mixed_type_name : name :=
  "Mixed<$T, `N>"%cpp_name.

Definition alias_name : name :=
  "Alias<$T>"%cpp_name.

Definition bare_alias_name : name :=
  "Alias"%cpp_name.

Definition value_alias_name : name :=
  "ValueAlias<`N>"%cpp_name.

Definition value_array_alias_name : name :=
  "ValueArrayAlias<`N>"%cpp_name.

Definition apply_alias_name : name :=
  Ninst (Nglobal (Nid "ApplyAlias"))
    [Atemplate_param "TemplateParam"; Atype (Tparam "T")].

Definition templated_var_name : name :=
  "templated_var<$T>"%cpp_name.

Definition bare_templated_var_name : name :=
  "templated_var"%cpp_name.

Definition uses_template_template_name : name :=
  Ninst (Nglobal (Nid "UsesTemplateTemplate"))
    [Atemplate_param "TemplateParam"; Atype (Tparam "T")].

Definition variadic_count_name : name :=
  Ninst
    (Nglobal (Nfunction function_qualifiers.N "variadic_count"
      [Tunsupported "PackExpansion Ts..."]))
    [Aunsupported "template parameter pack"].

Definition aggregate_value_name : name :=
  "aggregate_value<`V>()"%cpp_name.

Definition agg : type := "Agg"%cpp_type.

Example type_template_param_is_not_global_T :
  symbol_template_params type_shadow_name = Some [Ptype "T"].
Proof. vm_compute. reflexivity. Qed.

Example value_template_param_is_not_global_N :
  symbol_template_params value_shadow_name = Some [Pvalue "N" Tint].
Proof. vm_compute. reflexivity. Qed.

Example type_template_param_body_uses_function_parameter :
  lookup_function_template_body type_shadow_name =
  Some (Sseq [
    Sreturn (Some (Evar "value" (Tparam "T")))
  ]).
Proof. vm_compute. reflexivity. Qed.

Example value_template_param_body_uses_template_value :
  lookup_function_template_body value_shadow_name =
  Some (Sseq [
    Sreturn (Some (Eparam "N"))
  ]).
Proof. vm_compute. reflexivity. Qed.

Example nested_class_template_params :
  type_template_params nested_type_name = Some [Ptype "Outer"].
Proof. vm_compute. reflexivity. Qed.

Example nested_member_template_params :
  symbol_template_params nested_method_name = Some [Ptype "Outer"; Ptype "Inner"].
Proof. vm_compute. reflexivity. Qed.

Example nested_member_body_uses_inner_parameter :
  lookup_method_template_body nested_method_name =
  Some (Sseq [
    Sreturn (Some (Evar "inner" (Tparam "Inner")))
  ]).
Proof. vm_compute. reflexivity. Qed.

Example mixed_type_and_value_template_params :
  type_template_params mixed_type_name = Some [Ptype "T"; Pvalue "N" Tint].
Proof. vm_compute. reflexivity. Qed.

Example alias_template_params_are_preserved :
  alias_template_params alias_name = Some [Ptype "T"].
Proof. vm_compute. reflexivity. Qed.

Example alias_template_is_not_stored_under_bare_name :
  alias_template_params bare_alias_name = None.
Proof. vm_compute. reflexivity. Qed.

Example value_alias_template_params_are_preserved :
  alias_template_params value_alias_name = Some [Pvalue "N" Tint].
Proof. vm_compute. reflexivity. Qed.

Example value_array_alias_template_params_are_preserved :
  alias_template_params value_array_alias_name = Some [Pvalue "N" Tint].
Proof. vm_compute. reflexivity. Qed.

Example apply_alias_template_params_are_preserved :
  alias_template_params apply_alias_name =
  Some [Ptemplate "TemplateParam" [Ptype "T"]; Ptype "T"].
Proof. vm_compute. reflexivity. Qed.

Example concrete_alias_from_template_alias_resolves :
  RESOLVE_VALUE "takes_ptr(ConcreteAliasPtr)" "takes_ptr(int*)".
Proof. vm_compute. reflexivity. Qed.

Example concrete_alias_chain_from_template_alias_resolves :
  RESOLVE_VALUE "takes_ptr(ConcreteAliasChain)" "takes_ptr(int*)".
Proof. vm_compute. reflexivity. Qed.

Example concrete_member_template_alias_resolves :
  RESOLVE_VALUE "takes_ptr(ConcreteMemberPtr)" "takes_ptr(int*)".
Proof. vm_compute. reflexivity. Qed.

Example concrete_scoped_template_alias_resolves :
  RESOLVE_VALUE "takes_ptr(AliasNS::ConcreteScopedPtr)" "takes_ptr(int*)".
Proof. vm_compute. reflexivity. Qed.

Example concrete_nested_template_alias_resolves :
  RESOLVE_VALUE "takes_nested_ptr(ConcreteNestedPtr)" "takes_nested_ptr(int**)".
Proof. vm_compute. reflexivity. Qed.

Example direct_template_alias_should_resolve :
  RESOLVE_VALUE "takes_ptr(Alias<int>)" "takes_ptr(int*)".
Proof. vm_compute. reflexivity. Qed.

Example chained_template_alias_should_resolve :
  RESOLVE_VALUE "takes_ptr(AliasChain<int>)" "takes_ptr(int*)".
Proof. vm_compute. reflexivity. Qed.

Example scoped_template_alias_should_resolve :
  RESOLVE_VALUE "takes_ptr(AliasNS::ScopedAlias<int>)" "takes_ptr(int*)".
Proof. vm_compute. reflexivity. Qed.

Example member_template_alias_should_resolve :
  RESOLVE_VALUE "takes_ptr(AliasHolder::MemberAlias<int>)" "takes_ptr(int*)".
Proof. vm_compute. reflexivity. Qed.

Example const_template_alias_should_resolve :
  RESOLVE_VALUE "takes_const_ptr(ConstAlias<int>)" "takes_const_ptr(const int*)".
Proof. vm_compute. reflexivity. Qed.

Example reference_template_alias_should_resolve :
  RESOLVE_VALUE "takes_ref(RefAlias<int>)" "takes_ref(int&)".
Proof. vm_compute. reflexivity. Qed.

Example value_template_alias_should_resolve :
  RESOLVE_VALUE "takes_value_alias(ValueAlias<3>)" "takes_value_alias(int)".
Proof. vm_compute. reflexivity. Qed.

Example value_array_template_alias_should_resolve :
  RESOLVE_VALUE "takes_value_array_alias(ValueArrayAlias<3>&)"
                "takes_value_array_alias(int[3]&)".
Proof. vm_compute. reflexivity. Qed.

Example template_template_alias_should_resolve :
  RESOLVE_VALUE "takes_apply_alias(ApplyAlias<template Alias, int>)"
                "takes_apply_alias(int*)".
Proof. vm_compute. reflexivity. Qed.

Example variable_template_params_are_preserved :
  symbol_template_params templated_var_name = Some [Ptype "T"].
Proof. vm_compute. reflexivity. Qed.

Example variable_template_is_not_stored_under_bare_name :
  symbol_template_params bare_templated_var_name = None.
Proof. vm_compute. reflexivity. Qed.

Example template_template_param_is_preserved :
  type_template_params uses_template_template_name =
  Some [Ptemplate "TemplateParam" [Ptype "T"]; Ptype "T"].
Proof. vm_compute. reflexivity. Qed.

Example variadic_template_param_is_explicitly_recorded :
  symbol_template_params variadic_count_name =
  Some [Punsupported "template parameter pack"].
Proof. vm_compute. reflexivity. Qed.

Example variadic_body_resolves_function_pack :
  lookup_function_template_body variadic_count_name =
  Some (Sseq [
    Sreturn (Some (Ecast (Cintegral Tint) (Esizeof_pack None "values" Tulong)))
  ]).
Proof. vm_compute. reflexivity. Qed.

Example aggregate_value_template_param_is_preserved :
  symbol_template_params aggregate_value_name = Some [Pvalue "V" agg].
Proof. vm_compute. reflexivity. Qed.

Example aggregate_value_body_uses_template_value :
  lookup_function_template_body aggregate_value_name =
  Some (Sseq [
    Sreturn (Some (Ecast Cl2r
      (Emember false (Eparam "V") (Field (field_name.Id "a") false Tint))))
  ]).
Proof. vm_compute. reflexivity. Qed.
