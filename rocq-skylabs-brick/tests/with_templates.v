Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import skylabs.lang.cpp.syntax.translation_unit.
Require Import skylabs.lang.cpp.syntax.namemap.

#[with_templates]
cpp.prog templated prog cpp:{{
template <typename T> T id(T x) { return x; }
int use() { return id<int>(3); }
}}.

Example has_template_symbols :
  List.length (TM.elements templated.(translation_unit.msymbols)) = 1 := eq_refl.
