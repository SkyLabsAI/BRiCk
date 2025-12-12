(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.lang.cpp.syntax.prelude.
Require Import bluerock.lang.cpp.syntax.core.

(* parsing the left will produce the righ *and* printing the right will produce the left *)
Definition canonical : list (PrimString.string * name) :=
  let Msg : name := Nglobal $ Nid "Msg" in
  [ ("Msg", Msg)
  ; ("Msg::@0", (Nscoped Msg (Nanon 0)))
  ; ("Msg::Msg()", (Nscoped Msg (Nctor [])))
  ; ("Msg::~Msg()", (Nscoped Msg Ndtor))
  ; ("Msg::Msg(int)", (Nscoped Msg (Nctor [Tint])) )
  ; ("Msg::Msg(long)", (Nscoped Msg (Nctor [Tlong])) )
  ; ("Msg::operator=(const Msg&)", (Nscoped Msg (Nop function_qualifiers.N OOEqual [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator<(const Msg&)", (Nscoped Msg (Nop function_qualifiers.N OOLess [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator>(const Msg&)", (Nscoped Msg (Nop function_qualifiers.N OOGreater [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator==(const Msg&)", (Nscoped Msg (Nop function_qualifiers.N OOEqualEqual [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator!=(const Msg&)", (Nscoped Msg (Nop function_qualifiers.N OOExclaimEqual [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator<=(const Msg&)", (Nscoped Msg (Nop function_qualifiers.N OOLessEqual [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator>=(const Msg&)", (Nscoped Msg (Nop function_qualifiers.N OOGreaterEqual [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator>>=(const Msg&)", (Nscoped Msg (Nop function_qualifiers.N OOGreaterGreaterEqual [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator<<=(const Msg&)", (Nscoped Msg (Nop function_qualifiers.N OOLessLessEqual [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator+=(const Msg&)", (Nscoped Msg (Nop function_qualifiers.N OOPlusEqual [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator-=(const Msg&)", (Nscoped Msg (Nop function_qualifiers.N OOMinusEqual [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator*=(const Msg&)", (Nscoped Msg (Nop function_qualifiers.N OOStarEqual [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator/=(const Msg&)", (Nscoped Msg (Nop function_qualifiers.N OOSlashEqual [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator%=(const Msg&)", (Nscoped Msg (Nop function_qualifiers.N OOPercentEqual [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator|=(const Msg&)", (Nscoped Msg (Nop function_qualifiers.N OOPipeEqual [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator&=(const Msg&)", (Nscoped Msg (Nop function_qualifiers.N OOAmpEqual [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator^=(const Msg&)", (Nscoped Msg (Nop function_qualifiers.N OOCaretEqual [Tref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )

  ; ("Msg::operator=(const Msg&&)", (Nscoped Msg (Nop function_qualifiers.N OOEqual [Trv_ref (Tconst (Tnamed $ Nglobal (Nid "Msg")))])) )
  ; ("Msg::operator new()", (Nscoped Msg (Nop function_qualifiers.N (OONew false) [])) )
  ; ("Msg::operator new[]()", (Nscoped Msg (Nop function_qualifiers.N (OONew true) [])) )
  ; ("Msg::operator delete[]()", (Nscoped Msg (Nop function_qualifiers.N (OODelete true) [])) )
  ; ("Msg::operator int()", (Nscoped Msg (Nop_conv function_qualifiers.N Tint)) )
  ; ("foo_client(int[2]&, const int*, bool*, int**, char*)", (Nglobal (Nfunction function_qualifiers.N "foo_client" [Tref (Tarray Tint 2); Tptr (Tconst Tint); Tptr Tbool; Tptr (Tptr Tint); Tptr Tchar])) )
  ; ("DlistInternal::iterator::operator!=(const DlistInternal::iterator&) const",
                 (Nscoped (Nscoped (Nglobal (Nid "DlistInternal")) (Nid "iterator"))
                    (Nop function_qualifiers.Nc OOExclaimEqual [Tref (Tqualified QC (Tnamed (Nscoped (Nglobal (Nid "DlistInternal")) (Nid "iterator"))))])))
  ; ("intrusive::List_internal::iterator::iterator(intrusive::List_internal::Node*)",
                 (Nscoped (Nscoped (Nscoped (Nglobal (Nid "intrusive")) (Nid "List_internal")) (Nid "iterator"))
                    (Nctor [Tptr (Tnamed (Nscoped (Nscoped (Nglobal (Nid "intrusive")) (Nid "List_internal")) (Nid "Node")))])))
  ; ("integral", (Nglobal $ Nid "integral") )
  ; ("f<int>(int, int)", (Ninst (Nglobal $ Nfunction function_qualifiers.N "f" [Tint; Tint]) [Atype Tint]) )
  ; ("f<int>(enum @1, enum en)", (Ninst (Nglobal $ Nfunction function_qualifiers.N "f" [Tenum (Nglobal (Nanon 1)); Tenum (Nglobal (Nid "en"))]) [Atype Tint]))
  ; ("submit(unsigned long, std::function<void()>)",
      Nglobal
            (Nfunction function_qualifiers.N "submit"
               [Tnum int_rank.Ilong Unsigned; Tnamed (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "function")) [Atype (Tfunction (FunctionType Tvoid []))])]))
  ; ("submit(unsigned long, std::function<void(long, int, ...)>)",
      (Nglobal
         (Nfunction function_qualifiers.N "submit"
            [Tnum int_rank.Ilong Unsigned; Tnamed (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "function")) [Atype (Tfunction (FunctionType (ft_arity:=Ar_Variadic) Tvoid [Tlong; Tint]))])])))
  ; ("C<1, 0>", (Ninst (Nglobal (Nid "C")) [Avalue (Eint 1 Tint); Avalue (Eint 0 Tint)]) )
  ; ("C<1b, 0b>", (Ninst (Nglobal (Nid "C")) [Avalue (Eint 1 Tbool); Avalue (Eint 0 Tbool)]) )
    (* this is not actually valid C++ syntax but it is necessary in order to parse names without context *)
  ; ("C<1, ...<int, long>>", Ninst (Nglobal (Nid "C")) [Avalue (Eint 1 Tint); Apack [Atype Tint; Atype Tlong]])
  ; ("C<template CC>", Ninst (Nglobal (Nid "C")) [Atemplate (Nglobal (Nid "CC"))])
  ; ("C<template CC::foo, int>", Ninst (Nglobal (Nid "C")) [Atemplate (Nscoped (Nglobal (Nid "CC")) (Nid "foo")); Atype Tint])
  ; ("foo($T)", Nglobal (Nfunction function_qualifiers.N "foo" [Tparam "T"]))
  ; ("foo(typename $T::nested)", Nglobal (Nfunction function_qualifiers.N "foo" [Tnamed (Nscoped (Ndependent (Tparam "T")) (Nid "nested"))]))
  ]%pstring.

(* parsing the left will produce the right *)
Definition parse_only : list (PrimString.string * name) :=
  let Msg : name := Nglobal $ Nid "Msg" in
  [ ("::Msg", Msg)
  ; ("Msg::operator   delete()", (Nscoped Msg (Nop function_qualifiers.N (OODelete false) [])) )
  ; ("span<const int, 1ul>::span(const int*, unsigned long)",
        (Nscoped (Ninst (Nglobal (Nid "span")) [Atype (Tqualified QC Tint);
                                                Avalue (Eint 1 Tulong)])
           (Nctor [Tptr (Tqualified QC Tint); Tulong])))
  ; let targs := Avalue <$> [Eint 1 Tulong;
                              Eint (-2) Tlong;
                              Eint 3 Tulonglong;
                              Eint (-4) Tlonglong;
                              Eint 5 Tuint;
                              Eint 6 Tint] in
    ("Msg<1ul, -2l, 3ull, -4ll, 5u, 6>::Msg()", (Nscoped (Ninst Msg targs) (Nctor [])))
  ; let targs := Atype <$> [Tulong;
                            Tlong;
                            Tulonglong;
                            Tlonglong;
                            Tuint; Tint] in
    ("Msg<unsigned long, long, unsigned long long, long long, unsigned int, int>::Msg()", (Nscoped (Ninst Msg targs) (Nctor [])))
  ; ("foo_client(int[2]&, const int*, bool*, int**, char*)", (Nglobal (Nfunction function_qualifiers.N "foo_client" [Tref (Tarray Tint 2); Tptr (Tconst Tint); Tptr Tbool; Tptr (Tptr Tint); Tptr Tchar])) )
  ]%pstring.
