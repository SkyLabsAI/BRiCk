Example unresolved_prvalue_typed :
  unresolved_prvalue = Eunsupported "template parameter" Tint := eq_refl.
Example unresolved_lvalue_typed :
  unresolved_lvalue = Eunsupported "template parameter" (Tref Tint) := eq_refl.
Example unresolved_xvalue_typed :
  unresolved_xvalue = Eunsupported "template parameter" (Trv_ref Tint) := eq_refl.
Example wrong_kind_typed :
  wrong_kind = Eunsupported "type template parameter T" Tint := eq_refl.
Example unsupported_argument_typed :
  unsupported_argument = Eunsupported "TemplateParam Type" Tint := eq_refl.
