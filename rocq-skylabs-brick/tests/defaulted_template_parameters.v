Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.syntax.templates.
Require Import skylabs.lang.cpp.parser.
Require Import skylabs.lang.cpp.syntax.dealias.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.

#[with_templates]
cpp.prog source flags "-std=c++20" prog cpp:{{
template <typename T>
using Alias = T *;

template <typename T = int>
struct DefaultType {};

template <int N = 42>
struct DefaultValue {};

template <typename T = int>
using DefaultAlias = T *;

using ConcreteDefaultAlias = DefaultAlias<>;

void takes_ptr(int *);

template <typename T = int>
T defaulted_var = {};

template <template <typename X> class TemplateParam = Alias, typename T = int>
struct DefaultTemplateTemplate {
  TemplateParam<T> value;
};
}}.

Definition lookup_symbol_template (n : name) : option (template ObjValue) :=
  translation_unit.msymbols source !! n.

Definition lookup_type_template (n : name) : option (template GlobDecl) :=
  translation_unit.mtypes source !! n.

Definition symbol_template_params (n : name) : option (list _) :=
  match lookup_symbol_template n with
  | Some t => Some t.(template_params)
  | None => None
  end.

Definition type_template_params (n : name) : option (list _) :=
  match lookup_type_template n with
  | Some t => Some t.(template_params)
  | None => None
  end.

Definition alias_template_params (n : name) : option (list _) :=
  match translation_unit.maliases source !! n with
  | Some t => Some t.(template_params)
  | None => None
  end.

Notation RESOLVE_VALUE input output :=
  (trace.runO (dealias.resolveValue source input%cpp_name) = Some output%cpp_name)
  (only parsing).

Definition default_type_name : name :=
  "DefaultType<$T>"%cpp_name.

Definition default_value_name : name :=
  "DefaultValue<`N>"%cpp_name.

Definition default_alias_name : name :=
  "DefaultAlias<$T>"%cpp_name.

Definition defaulted_var_name : name :=
  "defaulted_var<$T>"%cpp_name.

Definition default_template_template_name : name :=
  Ninst (Nglobal (Nid "DefaultTemplateTemplate"))
    [Atemplate_param "TemplateParam"; Atype (Tparam "T")].

Example type_template_default_is_preserved :
  type_template_params default_type_name =
  Some [(Ptype "T", Some (Atype Tint))].
Proof. vm_compute. reflexivity. Qed.

Example value_template_default_is_preserved :
  type_template_params default_value_name =
  Some [(Pvalue "N" Tint, Some (Avalue (Eint 42%Z Tint)))].
Proof. vm_compute. reflexivity. Qed.

Example alias_template_default_is_preserved :
  alias_template_params default_alias_name =
  Some [(Ptype "T", Some (Atype Tint))].
Proof. vm_compute. reflexivity. Qed.

Example variable_template_default_is_preserved :
  symbol_template_params defaulted_var_name =
  Some [(Ptype "T", Some (Atype Tint))].
Proof. vm_compute. reflexivity. Qed.

Example template_template_default_is_preserved :
  type_template_params default_template_template_name =
  Some [
    (Ptemplate "TemplateParam" [Ptype "X"],
     Some (Atemplate (Nglobal (Nid "Alias"))));
    (Ptype "T", Some (Atype Tint))
  ].
Proof. vm_compute. reflexivity. Qed.

Example defaulted_alias_should_resolve :
  RESOLVE_VALUE "takes_ptr(ConcreteDefaultAlias)" "takes_ptr(int*)".
Proof. vm_compute. reflexivity. Qed.
