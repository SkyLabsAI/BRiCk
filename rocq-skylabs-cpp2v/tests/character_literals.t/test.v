Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require test.test_cpp.

Definition return_expr (nm : ident) : option Expr :=
  match test_cpp.source.(symbols) !! Nglobal (Nfunction function_qualifiers.N nm []) with
  | Some (Ofunction f) =>
      match f.(f_body) with
      | Some (Impl (Sseq [Sreturn (Some e)])) => Some e
      | _ => None
      end
  | _ => None
  end.

Example high_char_code_unit : return_expr "high_char" = Some (Echar 255 "char") :=
  ltac:(vm_compute; reflexivity).
Example ascii_code_unit : return_expr "ascii_char" = Some (Echar 65 "char") :=
  ltac:(vm_compute; reflexivity).
Example utf8_code_unit : return_expr "utf8_char" = Some (Echar 255 "char8_t") :=
  ltac:(vm_compute; reflexivity).
Example utf16_code_unit : return_expr "utf16_char" = Some (Echar 65535 "char16_t") :=
  ltac:(vm_compute; reflexivity).
Example utf32_code_unit : return_expr "utf32_char" = Some (Echar 128578 "char32_t") :=
  ltac:(vm_compute; reflexivity).
Example wide_code_unit : return_expr "wide_char" = Some (Echar 65535 "wchar_t") :=
  ltac:(vm_compute; reflexivity).
Example multichar_int : return_expr "multichar" = Some (Eint 16706 "int") :=
  ltac:(vm_compute; reflexivity).
Example negative_multichar_int : return_expr "negative_multichar" = Some (Eint (-1) "int") :=
  ltac:(vm_compute; reflexivity).
