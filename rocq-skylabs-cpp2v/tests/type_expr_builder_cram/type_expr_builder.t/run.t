  $ . ../../setup-cpp2v.sh
  $ probe=../../../build-dune-tests/cpp2v-type-expr-builder-probe
  $ "$probe" fixture.cpp -- -std=c++17 -fblocks > first.out
  $ grep -v -E '^(OP_|CALL_|INIT_|ALLOC_|LAMBDA_|COND_|STMT_|LOCAL_|VLA_)' first.out
  NAME (Nglobal (core.Nfunction function_qualifiers.N "normalized" ((Tptr (Tqualified QC (Tnum int_rank.Iint Signed))) :: (Tptr (core.Tfunction (@FunctionType _ CC_C Ar_Definite (Tnum int_rank.Iint Signed) ((Tnum int_rank.Iint Signed) :: nil)))) :: (Tptr (Tnum int_rank.Iint Signed)) :: nil)))
  NAME (Nscoped (Nglobal (Nid "C")) (core.Nctor ((Tptr (Tqualified QC (Tnum int_rank.Iint Signed))) :: nil)))
  NAME (Nscoped (Nglobal (Nid "C")) (Ndtor))
  NAME (Nscoped (Nglobal (Nid "C")) (Nop_conv function_qualifiers.Nc (Tptr (Tqualified QC (Tnum int_rank.Iint Signed)))))
  NAME (Nscoped (Nglobal (Nid "C")) (core.Nop function_qualifiers.Nc OOPlus ((Tptr (Tqualified QC (Tnum int_rank.Iint Signed))) :: nil)))
  NAME (Ninst (Nglobal (Nid "Primary")) ((Atype (Tparam "T")) :: (Avalue (Eparam "N")) :: (Atemplate_param "TT") :: nil))
  NAME (Ninst (Nglobal (Nid "Primary")) ((Atype (Tptr (Tparam "T"))) :: (Avalue (Eparam "N")) :: (Atemplate_param "__template_0_2") :: nil))
  NAME (Ninst (Nglobal (Nid "Primary")) ((Atype (Tnum int_rank.Ilong Signed)) :: (Avalue (Eint 2 (Tnum int_rank.Iint Signed))) :: (Atemplate (Nglobal (Nid "DefaultBox"))) :: nil))
  NAME (Ninst (Nglobal (core.Nfunction function_qualifiers.N "function_template" ((Tptr (Tqualified QC (Tnum int_rank.Iint Signed))) :: nil))) ((Atype (Tnum int_rank.Iint Signed)) :: nil))
  NAME (Ninst (Nglobal (Nid "variable_template")) ((Atype (Tnum int_rank.Iint Signed)) :: nil))
  NAME (Nglobal (core.Nop function_qualifiers.N (OONew false) ((Tnum int_rank.Ilong Unsigned) :: nil)))
  NAME (Nglobal (core.Nop function_qualifiers.N (OODelete true) ((Tptr (Tvoid)) :: nil)))
  NAME (Ninst (Nglobal (Nid "Primary")) ((Atype (Tnum int_rank.Iint Signed)) :: (Avalue (Eint 3 (Tnum int_rank.Iint Signed))) :: (Atemplate (Nglobal (Nid "DefaultBox"))) :: nil))
  NAME (Ninst (Nglobal (core.Nfunction function_qualifiers.N "function_template" ((Tptr (Tqualified QC (Tparam "T"))) :: nil))) ((Atype (Tparam "T")) :: nil))
  NAME (Ninst (Nglobal (Nid "variable_template")) ((Atype (Tparam "T")) :: nil))
  NAME (Ninst (Nglobal (Nid "AliasTemplate")) ((Atype (Tparam "T")) :: nil))
  NAME (Ninst (Nglobal (Nid "ApplyTemplate")) ((Atemplate_param "TT") :: (Atype (Tparam "T")) :: nil))
  TYPE (Tptr (Tqualified QC (Tnum int_rank.Iint Signed)))
  TYPE (Tarray (Tnum int_rank.Iint Signed) 4)
  TYPE (Tptr (core.Tfunction (@FunctionType _ CC_C Ar_Definite (Tnum int_rank.Iint Signed) ((Tnum int_rank.Iint Signed) :: nil))))
  TYPE (Tmember_pointer (Tnamed (Nglobal (Nid "C"))) (Tnum int_rank.Iint Signed))
  TYPE (Tnum int_rank.Iint Signed)
  TYPE (core.Tfunction (@FunctionType _ CC_C Ar_Definite (Tnum int_rank.Iint Signed) ((Tptr (Tqualified QC (Tnum int_rank.Iint Signed))) :: (Tptr (core.Tfunction (@FunctionType _ CC_C Ar_Definite (Tnum int_rank.Iint Signed) ((Tnum int_rank.Iint Signed) :: nil)))) :: (Tptr (Tnum int_rank.Iint Signed)) :: nil)))
  TYPE (Tunsupported "Builtin long double")
  TYPE (core.Tfunction (@FunctionType _ CC_C Ar_Definite (Tunsupported "Auto auto") nil))
  TYPE (core.Tfunction (@FunctionType _ CC_C Ar_Definite (Tauto) nil))
  TYPE (Tnamed (Nscoped (core.Ndependent (Tparam "T")) (Nid "type")))
  TYPE (Tunsupported "TemplateSpecialization typename T::template rebind<int>")
  TYPE (Tnum int_rank.Iint Unsigned)
  TYPE (Tunsupported "Auto auto")
  TYPE (Tnum int_rank.Iint Signed)
  TYPE (Tref (Tnum int_rank.Iint Signed))
  TYPE (Tnamed (Nglobal (Nid "C")))
  TYPE (Tunsupported "Vector __attribute__((__vector_size__(4 * sizeof(int)))) int")
  TYPE (Tunsupported "BlockPointer int (^)(int)")
  TYPE (Tptr (Tnum int_rank.Iint Signed))
  TYPE (Tnamed (Ninst (Nglobal (Nid "PackTarget")) ((Atype (Tunsupported "PackExpansion Ts...")) :: nil)))
  TYPE (Tdecltype (Eunresolved_global (Nscoped (core.Ndependent (Tparam "T")) (Nid "value"))))
  TYPE (Tdecltype (Eunresolved_global (Nscoped (core.Ndependent (Tparam "T")) (Nid "value"))))
  TYPE (Tnamed (Ninst (Nglobal (Nid "InjectedAudit")) ((Atype (Tparam "T")) :: nil)))
  TYPE (Tnamed (Ninst (core.Ndependent (Tparam "TT")) ((Atype (Tparam "T")) :: nil)))
  TYPE (Tunsupported "Decltype decltype(T::value)")
  TYPE (Tunsupported "Decltype decltype((T::value))")
  TYPE (Tvariable_array (Tnum int_rank.Iint Signed) (core.Ebinop Badd (Ecast (Cl2r) (Evar "bound" (Tnum int_rank.Iint Signed))) (Eint 1 (Tnum int_rank.Iint Signed)) (Tnum int_rank.Iint Signed)))
  TYPE (Tptr (Tnum int_rank.Iint Signed))
  TYPE (Tptr (Tqualified QC (Tnum int_rank.Iint Signed)))
  EXPR (Eint 42 (Tnum int_rank.Iint Signed))
  EXPR (Ebool true)
  EXPR (core.Estring (literal_string.of_list_N (104%N :: 105%N :: nil)) (Tchar_ char_type.Cchar))
  EXPR (Enull)
  EXPR (Eglobal (Nglobal (Nid "ordinary")) (Tnum int_rank.Iint Signed))
  EXPR (Ecast (Cbuiltin2fun (Tptr (core.Tfunction (@FunctionType _ CC_C Ar_Definite (Tnum int_rank.Ilong Unsigned) ((Tptr (Tqualified QC (Tchar_ char_type.Cchar))) :: nil))))) (Eglobal (Nglobal (Nid "__builtin_strlen")) (core.Tfunction (@FunctionType _ CC_C Ar_Definite (Tnum int_rank.Ilong Unsigned) ((Tptr (Tqualified QC (Tchar_ char_type.Cchar))) :: nil)))))
  EXPR (core.Eunop Uminus (Eint 2 (Tnum int_rank.Iint Signed)) (Tnum int_rank.Iint Signed))
  EXPR (core.Ebinop Badd (core.Eunop Uminus (Eint 2 (Tnum int_rank.Iint Signed)) (Tnum int_rank.Iint Signed)) (Eint 1 (Tnum int_rank.Iint Signed)) (Tnum int_rank.Iint Signed))
  EXPR (core.Eunop Uminus (Eparam "N") (Tnum int_rank.Iint Signed))
  EXPR (core.Ebinop Badd (Eparam "N") (Eint 1 (Tnum int_rank.Iint Signed)) (Tnum int_rank.Iint Signed))
  EXPR (Eunresolved_global (Nscoped (core.Ndependent (Tparam "T")) (Nid "value")))
  EXPR (Evar "named_local" (Tnum int_rank.Iint Signed))
  EXPR (Eglobal (Nscoped (Nglobal (core.Nfunction function_qualifiers.N "local_reference_kernel" nil)) (Nid "static_local")) (Tnum int_rank.Iint Signed))
  EXPR (core.Ebinop Badd (Ecast (Cl2r) (Evar "named_local" (Tnum int_rank.Iint Signed))) (Ecast (Cl2r) (Eglobal (Nscoped (Nglobal (core.Nfunction function_qualifiers.N "local_reference_kernel" nil)) (Nid "static_local")) (Tnum int_rank.Iint Signed))) (Tnum int_rank.Iint Signed))
  EXPR (Evar "reference_local" (Tref (Tnum int_rank.Iint Signed)))
  EXPR (Evar "binding_value" (Tnum int_rank.Iint Signed))
  EXPR (Eenum_const (Nglobal (Nid "KernelEnum")) "KFirst")
  EXPR (Ecast (Cintegral (Tnum int_rank.Iint Signed)) (Eenum_const (Nglobal (Nid "KernelEnum")) "KFirst"))
  EXPR (Eglobal (Nglobal (Nid "__builtin_strlen")) (core.Tfunction (@FunctionType _ CC_C Ar_Definite (Tnum int_rank.Ilong Unsigned) ((Tptr (Tqualified QC (Tchar_ char_type.Cchar))) :: nil))))
  EXPR (Ecast (Cintegral (Tnum int_rank.Ilong Signed)) (Ecast (Cl2r) (Eglobal (Nglobal (Nid "cast_source")) (Tnum int_rank.Iint Signed))))
  EXPR (Ecast (Cptr2bool) (Ecast (Cl2r) (Eglobal (Nglobal (Nid "cast_pointer")) (Tptr (Tnum int_rank.Iint Signed)))))
  EXPR (Ecast (Cint2bool) (Ecast (Cl2r) (Eglobal (Nglobal (Nid "cast_source")) (Tnum int_rank.Iint Signed))))
  EXPR (Ecast (Cfloat2bool) (Efloat float_type.Fdouble (float_value.of_bits float_type.Fdouble 4607182418800017408)))
  EXPR (Ecast (Cint2float (Tfloat_ float_type.Fdouble)) (Ecast (Cl2r) (Eglobal (Nglobal (Nid "cast_source")) (Tnum int_rank.Iint Signed))))
  EXPR (Ecast (Cfloat2int (Tnum int_rank.Iint Signed)) (Ecast (Cl2r) (Eglobal (Nglobal (Nid "cast_double_source")) (Tfloat_ float_type.Fdouble))))
  EXPR (Ecast (Cfloat (Tfloat_ float_type.Ffloat)) (Efloat float_type.Fdouble (float_value.of_bits float_type.Fdouble 4609434218613702656)))
  EXPR (Ecast (Cnull2ptr (Tptr (Tvoid))) (Eint 0 (Tnum int_rank.Iint Signed)))
  EXPR (Ecast (Cnull2memberptr (Tmember_pointer (Tnamed (Nglobal (Nid "CastBase"))) (Tnum int_rank.Iint Signed))) (Enull))
  EXPR (Ecast (Cfun2ptr) (Eglobal (Nglobal (core.Nfunction function_qualifiers.N "cast_function" ((Tnum int_rank.Iint Signed) :: nil))) (core.Tfunction (@FunctionType _ CC_C Ar_Definite (Tnum int_rank.Iint Signed) ((Tnum int_rank.Iint Signed) :: nil)))))
  EXPR (Ecast (Carray2ptr) (Eglobal (Nglobal (Nid "cast_array")) (Tarray (Tnum int_rank.Iint Signed) 2)))
  EXPR (Eexplicit_cast cast_style.c (Tnum int_rank.Ilong Signed) (Ecast (Cnoop (Tnum int_rank.Ilong Signed)) (Ecast (Cintegral (Tnum int_rank.Ilong Signed)) (Ecast (Cl2r) (Eglobal (Nglobal (Nid "cast_source")) (Tnum int_rank.Iint Signed))))))
  EXPR (Eexplicit_cast cast_style.functional (Tnum int_rank.Ilong Signed) (Ecast (Cnoop (Tnum int_rank.Ilong Signed)) (Ecast (Cintegral (Tnum int_rank.Ilong Signed)) (Ecast (Cl2r) (Eglobal (Nglobal (Nid "cast_source")) (Tnum int_rank.Iint Signed))))))
  EXPR (Eexplicit_cast cast_style.static (Tnum int_rank.Ilong Signed) (Ecast (Cnoop (Tnum int_rank.Ilong Signed)) (Ecast (Cintegral (Tnum int_rank.Ilong Signed)) (Ecast (Cl2r) (Eglobal (Nglobal (Nid "cast_source")) (Tnum int_rank.Iint Signed))))))
  EXPR (Eexplicit_cast cast_style.reinterpret (Tnum int_rank.Ilong Unsigned) (Ecast (Cptr2int (Tnum int_rank.Ilong Unsigned)) (Ecast (Cl2r) (Eglobal (Nglobal (Nid "cast_pointer")) (Tptr (Tnum int_rank.Iint Signed))))))
  EXPR (Eexplicit_cast cast_style.const (Tptr (Tnum int_rank.Iint Signed)) (Ecast (Cnoop (Tptr (Tnum int_rank.Iint Signed))) (Ecast (Cl2r) (Eglobal (Nglobal (Nid "cast_const_pointer")) (Tptr (Tqualified QC (Tnum int_rank.Iint Signed)))))))
  EXPR (Eexplicit_cast cast_style.reinterpret (Tptr (Tchar_ char_type.Cchar)) (Ecast (Cbitcast (Tptr (Tchar_ char_type.Cchar))) (Ecast (Cl2r) (Eglobal (Nglobal (Nid "cast_pointer")) (Tptr (Tnum int_rank.Iint Signed))))))
  EXPR (Eexplicit_cast cast_style.reinterpret (Tref (Tnum int_rank.Iint Signed)) (Ecast (Clvaluebitcast (Tref (Tnum int_rank.Iint Signed))) (Eglobal (Nglobal (Nid "cast_bit_source")) (Tfloat_ float_type.Ffloat))))
  EXPR (Eexplicit_cast cast_style.reinterpret (Tptr (Tnum int_rank.Iint Signed)) (Ecast (Cint2ptr (Tptr (Tnum int_rank.Iint Signed))) (Eint 1 (Tnum int_rank.Ilong Unsigned))))
  EXPR (Eexplicit_cast cast_style.c (Tptr (Tnamed (Nglobal (Nid "CastBase")))) (Ecast (Cnoop (Tptr (Tnamed (Nglobal (Nid "CastBase"))))) (Ecast (Cderived2base ((Tnamed (Nglobal (Nid "CastMiddle"))) :: nil) (Tptr (Tnamed (Nglobal (Nid "CastBase"))))) (Ecast (Cl2r) (Eglobal (Nglobal (Nid "cast_derived")) (Tptr (Tnamed (Nglobal (Nid "CastDerived")))))))))
  EXPR (Eexplicit_cast cast_style.dynamic (Tptr (Tnamed (Nglobal (Nid "CastDerived")))) (Ecast (Cdynamic (Tptr (Tnamed (Nglobal (Nid "CastDerived"))))) (Ecast (Cl2r) (Eglobal (Nglobal (Nid "cast_base")) (Tptr (Tnamed (Nglobal (Nid "CastBase"))))))))
  EXPR (Eexplicit_cast cast_style.static (Tptr (Tnamed (Nglobal (Nid "CastBase")))) (Ecast (Cnoop (Tptr (Tnamed (Nglobal (Nid "CastBase"))))) (Ecast (Cderived2base ((Tnamed (Nglobal (Nid "CastMiddle"))) :: nil) (Tptr (Tnamed (Nglobal (Nid "CastBase"))))) (Ecast (Cl2r) (Eglobal (Nglobal (Nid "cast_derived")) (Tptr (Tnamed (Nglobal (Nid "CastDerived")))))))))
  EXPR (Eexplicit_cast cast_style.static (Tptr (Tnamed (Nglobal (Nid "CastDerived")))) (Ecast (Cbase2derived ((Tnamed (Nglobal (Nid "CastMiddle"))) :: nil) (Tptr (Tnamed (Nglobal (Nid "CastDerived"))))) (Ecast (Cl2r) (Eglobal (Nglobal (Nid "cast_base")) (Tptr (Tnamed (Nglobal (Nid "CastBase"))))))))
  EXPR (Eexplicit_cast cast_style.functional (Tnum int_rank.Iint Unsigned) (Ecast (Cl2r_bitcast (Tnum int_rank.Iint Unsigned)) (Eglobal (Nglobal (Nid "cast_bit_source")) (Tfloat_ float_type.Ffloat))))
  EXPR (Eexplicit_cast cast_style.static (Tvoid) (Ecast (C2void) (Eglobal (Nglobal (Nid "cast_source")) (Tnum int_rank.Iint Signed))))
  EXPR (Echar 65%N (Tchar_ char_type.Cchar))
  EXPR (Echar 66%N (Tchar_ char_type.Cwchar))
  EXPR (Echar 67%N (Tchar_ char_type.C16))
  EXPR (Echar 68%N (Tchar_ char_type.C32))
  EXPR (Efloat float_type.Ffloat (float_value.of_bits float_type.Ffloat 1069547520))
  EXPR (Efloat float_type.Fdouble (float_value.of_bits float_type.Fdouble 4612811918334230528))
  EXPR (Eunsupported "unsupported floating-point semantics x87DoubleExtended for LongDouble: 3.5" (Tunsupported "Builtin long double"))
  EXPR (core.Estring (literal_string.of_list_N (65%N :: 90%N :: nil)) (Tchar_ char_type.Cwchar))
  EXPR (core.Estring (literal_string.of_list_N (65%N :: 90%N :: nil)) (Tchar_ char_type.C16))
  EXPR (core.Estring (literal_string.of_list_N (65%N :: 90%N :: nil)) (Tchar_ char_type.C32))
  EXPR (Ecast (Cptr2int (Tnum int_rank.Ilong Signed)) (Enull))
  EXPR (Eint 197 (Tnum int_rank.Iint Unsigned))
  EXPR (core.Estring (literal_string.of_list_N (102%N :: 105%N :: 120%N :: 116%N :: 117%N :: 114%N :: 101%N :: 46%N :: 99%N :: 112%N :: 112%N :: nil)) (Tchar_ char_type.Cchar))
  EXPR (Ebool false)
  EXPR (Ebool true)
  EXPR (core.Estring (literal_string.of_list_N (108%N :: 105%N :: 116%N :: 101%N :: 114%N :: 97%N :: 108%N :: 95%N :: 112%N :: 114%N :: 101%N :: 100%N :: 101%N :: 102%N :: 105%N :: 110%N :: 101%N :: 100%N :: nil)) (Tchar_ char_type.Cchar))
  EXPR (Eint 9 (Tnum int_rank.Iint Signed))
  EXPR (Eexplicit_cast cast_style.static (Tnum int_rank.Iint Signed) (Ecast (Cdependent (Tnum int_rank.Iint Signed)) (Evar "value" (Tparam "T"))))
  PARAM (Ptype "T")
  PARAM (Pvalue "N" (Tnum int_rank.Iint Signed))
  PARAM (Ptemplate "TT" ((Ptype "__type_1_0") :: nil))
  PARAM (Ptype "__type_0_0")
  PARAM (Ptype "T")
  PARAM (Pvalue "N" (Tnum int_rank.Iint Signed))
  PARAM (Ptemplate "TT" ((Ptype "__type_1_0") :: nil))
  ARG (Atype (Tptr (Tqualified QC (Tnum int_rank.Iint Signed))))
  ARG (Avalue (Eint 7 (Tnum int_rank.Iint Signed)))
  ARG (Avalue (Eaddrof (Eglobal (Nglobal (Nid "declaration_target")) (Tnum int_rank.Iint Signed))))
  ARG (Atype (Tptr (Tqualified QC (Tnum int_rank.Iint Signed))))
  ARG (Apack ((Atype (Tnum int_rank.Iint Signed)) :: (Atype (Tnum int_rank.Ilong Signed)) :: nil))
  ARG (Avalue (Eglobal (Nglobal (Nid "declaration_target")) (Tnum int_rank.Iint Signed)))
  ARG (Aunsupported "Null")
  ARG (Aunsupported "TemplateExpansion")
  DEFAULT (Atype (Tnum int_rank.Iint Signed))
  DEFAULT (Avalue (Eint 3 (Tnum int_rank.Iint Signed)))
  DEFAULT (Atemplate (Nglobal (Nid "DefaultBox")))
  DEFAULT (Atype (Tnum int_rank.Iint Signed))
  DEFAULT (Avalue (Eint 5 (Tnum int_rank.Iint Signed)))
  DEFAULT (Atemplate (Nglobal (Nid "DefaultBox")))

The emitted values are final core terms. In particular, the record constructor
uses an explicit application rather than relying on FunctionType's implicit
calling-convention and arity arguments. Compile all selected categories.

  $ { echo 'Require Import skylabs.lang.cpp.mparser.'; echo '#[local] Open Scope pstring_scope.'; for k in NAME TYPE EXPR OP_STATIC OP_TEMPLATE CALL_STATIC CALL_TEMPLATE INIT_STATIC INIT_TEMPLATE ALLOC_STATIC ALLOC_TEMPLATE LAMBDA_ATOMIC_STATIC LAMBDA_TEMPLATE LAMBDA_NESTED_STATIC LAMBDA_NESTED_TEMPLATE COND_STATIC COND_TEMPLATE STMT_EXPR LOCAL_STATIC LOCAL_TEMPLATE LOCAL_VLA_STATIC LOCAL_VLA_TEMPLATE STMT_STATIC STMT_TEMPLATE STMT_NULL VLA_STATIC VLA_TEMPLATE PARAM ARG DEFAULT; do case "$k" in NAME) ty=Mname;; TYPE) ty=Mtype;; EXPR|OP_STATIC|OP_TEMPLATE|CALL_STATIC|CALL_TEMPLATE|INIT_STATIC|INIT_TEMPLATE|ALLOC_STATIC|ALLOC_TEMPLATE|LAMBDA_ATOMIC_STATIC|LAMBDA_TEMPLATE|LAMBDA_NESTED_STATIC|LAMBDA_NESTED_TEMPLATE|COND_STATIC|COND_TEMPLATE|STMT_EXPR|VLA_STATIC|VLA_TEMPLATE) ty=MExpr;; LOCAL_STATIC|LOCAL_TEMPLATE|LOCAL_VLA_STATIC|LOCAL_VLA_TEMPLATE) ty=MVarDecl;; STMT_STATIC|STMT_TEMPLATE|STMT_NULL) ty=MStmt;; PARAM) ty=Mtemp_param;; ARG|DEFAULT) ty=Mtemp_arg;; esac; echo "Definition ir_${k} : list ${ty} := ("; grep "^${k} " first.out | sed "s/^${k} /  /; s/$/ ::/"; echo '  nil).'; done; } > check.v
  $ rocq c $ROCQC_ARGS check.v

The completed pre-switch audit proved this focused matrix equal to the
independent legacy printer. The permanent test now compiles every owned
final term; production has only the owned semantic implementation.

C++20 adds `char8_t` character and UTF-8 string literals and compiles the
corresponding owned terms without changing the C++17 matrix. A C++23 parse
additionally exercises the `if consteval` lowering and its
anchored synthetic missing-else node in the structural probe.

  $ "$probe" fixture.cpp -- -std=c++23 -fblocks >/dev/null 2>/dev/null

  $ "$probe" fixture.cpp -- -std=c++20 -fblocks > twenty.out 2>/dev/null
  $ { echo 'Require Import skylabs.lang.cpp.mparser.'; echo '#[local] Open Scope pstring_scope.'; for k in EXPR OP_STATIC OP_TEMPLATE CALL_STATIC CALL_TEMPLATE INIT_STATIC INIT_TEMPLATE ALLOC_STATIC ALLOC_TEMPLATE LAMBDA_ATOMIC_STATIC LAMBDA_TEMPLATE LAMBDA_NESTED_STATIC LAMBDA_NESTED_TEMPLATE COND_STATIC COND_TEMPLATE STMT_EXPR LOCAL_STATIC LOCAL_TEMPLATE LOCAL_VLA_STATIC LOCAL_VLA_TEMPLATE STMT_STATIC STMT_TEMPLATE STMT_NULL VLA_STATIC VLA_TEMPLATE; do case "$k" in LOCAL_STATIC|LOCAL_TEMPLATE|LOCAL_VLA_STATIC|LOCAL_VLA_TEMPLATE) ty=MVarDecl;; STMT_STATIC|STMT_TEMPLATE|STMT_NULL) ty=MStmt;; *) ty=MExpr;; esac; echo "Definition ir20_${k} : list ${ty} := ("; grep "^${k} " twenty.out | sed "s/^${k} /  /; s/$/ ::/"; echo '  nil).'; done; } > check20.v
  $ rocq c $ROCQC_ARGS check20.v

The diagnostic name path covers the comparable selected names independently. This catches array/function decay and top-level cv normalization.

  $ cpp2v --name-test=diagnostic_names.v fixture.cpp -- -std=c++17 -fblocks >/dev/null 2>&1
  $ rocq c $ROCQC_ARGS diagnostic_names.v
  $ cat >> check.v <<'EOF'
  > Require Import diagnostic_names.
  > Definition diagnostic_names : list Mname := List.app module_names template_names.
  > Definition diagnostic_has_name (n : Mname) : bool :=
  >   List.existsb (fun candidate => bool_decide (candidate = n)) diagnostic_names.
  > (* The diagnostic path covers all comparable selected names. *)
  > Definition comparable_ir_names :=
  >   List.app (List.firstn 6 ir_NAME) (List.skipn 7 ir_NAME).
  > Example diagnostic_names_complete :
  >   List.forallb diagnostic_has_name comparable_ir_names = true.
  > Proof. vm_compute. reflexivity. Qed.
  > EOF
  $ rocq c $ROCQC_ARGS check.v

The production output contains the corresponding final type/expression families.

  $ cpp2v -o production.v fixture.cpp -- -std=c++17 -fblocks >/dev/null 2>&1
  $ grep -Fq 'Tmember_pointer' production.v
  $ grep -Fq 'Tunsupported "UnaryTransform __decay(T)"' production.v
  $ grep -Fq 'Estring' production.v
  $ grep -Fq 'Ecast (Cbuiltin2fun' production.v
  $ grep -Fq 'Tunsupported "Builtin long double"' production.v
  $ grep -Fq 'Tunsupported "Vector __attribute__((__vector_size__(4 * sizeof(int)))) int"' production.v
  $ grep -Fq 'Tunsupported "BlockPointer int (^)(int)"' production.v
  $ grep -Fq 'Tunsupported "PackExpansion Ts..."' production.v

Repeated extraction is byte deterministic.

  $ "$probe" fixture.cpp -- -std=c++17 -fblocks > second.out
  $ cmp first.out second.out
  $ grep -q '^VLA_TEMPLATE .*Eunsupported "variable length array capture" (Tauto)' first.out
