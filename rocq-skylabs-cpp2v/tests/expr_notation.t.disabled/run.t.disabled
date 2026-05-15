  $ . ../setup-project.sh
  $ dune build test.vo
  local_ref = {e: $"FooBarBaz"}
       : Expr
  
  local_ref uses section variable ty.
  global_ref = {e: $::"FooBarBaz"}
       : Expr
  
  global_ref uses section variable ty.
  enum_const_ref = {e: $::"_ZN6MyEnumE"::"Const"}
       : Expr
  Echar_letter = {e: ASCII#65}
       : Expr
  
  Echar_letter uses section variable ty.
  Echar_newline = {e: ASCII#10}
       : Expr
  
  Echar_newline uses section variable ty.
  Estring_1 = {e: STRING#to_chars "FooBarBazQux"}
       : Expr
  
  Estring_1 uses section variable ty.
  Eint_1 = {e: #42}
       : Expr
  
  Eint_1 uses section variable ty.
  Eint_2 = {e: #314}
       : Expr
  
  Eint_2 uses section variable ty.
  Ebool_true = {e: #true}
       : Expr
  Ebool_false = {e: #false}
       : Expr
  {e: -}
       : UnOp
  {e: !}
       : UnOp
  {e: ~}
       : UnOp
  {e: {:unop:UNSUPPORTED:"FooBarBaz":}}
       : UnOp
  Eunop_1 = {e: -#42}
       : Expr
  
  Eunop_1 uses section variable ty.
  Eunop_2 = {e: !#false}
       : Expr
  
  Eunop_2 uses section variable ty.
  Eunop_3 = {e: ~#314}
       : Expr
  
  Eunop_3 uses section variable ty.
  Eunop_4 = {e: {:unop:UNSUPPORTED:"FooBarBaz":}{?: e}}
       : Expr
  
  Eunop_4 uses section variables ty e.
  {e: +}
       : BinOp
  {e: &}
       : BinOp
  {e: <=>}
       : BinOp
  {e: /}
       : BinOp
  {e: ==}
       : BinOp
  {e: >=}
       : BinOp
  {e: >}
       : BinOp
  {e: <=}
       : BinOp
  {e: <}
       : BinOp
  {e: *}
       : BinOp
  {e: !=}
       : BinOp
  {e: |}
       : BinOp
  {e: %}
       : BinOp
  {e: <<}
       : BinOp
  {e: -}
       : BinOp
  {e: ^}
       : BinOp
  {e: .*}
       : BinOp
  {e: ->*}
       : BinOp
  Ebinop_custom_Bdotp_nowrap = {e: ($"FooBarBaz".*$"Qux")}
       : Expr
  
  Ebinop_custom_Bdotp_nowrap uses section variable ty.
  Ebinop_custom_Bdotip_nowrap = {e: ($"FooBarBaz"->*$"Qux")}
       : Expr
  
  Ebinop_custom_Bdotip_nowrap uses section variable ty.
  Ebinop_custom_Bshr_nowrap = {e: (#314 >> #42)}
       : Expr
  
  Ebinop_custom_Bshr_nowrap uses section variable ty.
  Ebinop_custom_Bdotp_wrap =
  {e: ($"FooBarBazFooBarBazFooBarBazFooBarBazFooBarBazFooBarBazFooBarBazFooBarBazFooBarBazFooBarBaz"
         .*$"Qux")}
       : Expr
  
  Ebinop_custom_Bdotp_wrap uses section variable ty.
  Ebinop_custom_Bdotip_wrap =
  {e: ($"FooBarBazFooBarBazFooBarBazFooBarBazFooBarBazFooBarBazFooBarBazFooBarBazFooBarBaz"
         ->*$"Qux")}
       : Expr
  
  Ebinop_custom_Bdotip_wrap uses section variable ty.
  Ebinop_custom_Bshr_wrap =
  {e: (#31415926535897932384626433832795028841971693993751058209749445923078164062862089986280348253421170679
         >> #42)}
       : Expr
  
  Ebinop_custom_Bshr_wrap uses section variable ty.
  Ebinop_default_Badd = {e: (#42 + #314)}
       : Expr
  
  Ebinop_default_Badd uses section variable ty.
  Ebinop_default_Band = {e: (#42 & #314)}
       : Expr
  
  Ebinop_default_Band uses section variable ty.
  Ebinop_default_Bcmp = {e: (#42 <=> #314)}
       : Expr
  
  Ebinop_default_Bcmp uses section variable ty.
  Ebinop_default_Bdiv = {e: (#42 / #314)}
       : Expr
  
  Ebinop_default_Bdiv uses section variable ty.
  Ebinop_default_Beq = {e: (#42 == #314)}
       : Expr
  
  Ebinop_default_Beq uses section variable ty.
  Ebinop_default_Bge = {e: (#42 >= #314)}
       : Expr
  
  Ebinop_default_Bge uses section variable ty.
  Ebinop_default_Bgt = {e: (#42 > #314)}
       : Expr
  
  Ebinop_default_Bgt uses section variable ty.
  Ebinop_default_Ble = {e: (#42 <= #314)}
       : Expr
  
  Ebinop_default_Ble uses section variable ty.
  Ebinop_default_Blt = {e: (#42 < #314)}
       : Expr
  
  Ebinop_default_Blt uses section variable ty.
  Ebinop_default_Bmul = {e: (#42 * #314)}
       : Expr
  
  Ebinop_default_Bmul uses section variable ty.
  Ebinop_default_Bneq = {e: (#42 != #314)}
       : Expr
  
  Ebinop_default_Bneq uses section variable ty.
  Ebinop_default_Bor = {e: (#42 | #314)}
       : Expr
  
  Ebinop_default_Bor uses section variable ty.
  Ebinop_default_Bmod = {e: (#42 % #314)}
       : Expr
  
  Ebinop_default_Bmod uses section variable ty.
  Ebinop_default_Bshl = {e: (#42 << #314)}
       : Expr
  
  Ebinop_default_Bshl uses section variable ty.
  Ebinop_default_Bsub = {e: (#42 - #314)}
       : Expr
  
  Ebinop_default_Bsub uses section variable ty.
  Ebinop_default_Bxor = {e: (#42 ^ #314)}
       : Expr
  
  Ebinop_default_Bxor uses section variable ty.
  Ebinop_compound_1 = {e: ((#42 >> #2) << #314)}
       : Expr
  
  Ebinop_compound_1 uses section variable ty.
  Ebinop_compound_2 =
  {e: (#-1 * (($::"FOOBAR" ^ (#42 / #2)) - #314))}
       : Expr
  
  Ebinop_compound_2 uses section variable ty.
  Ederef_Evar = {e: *$"Qux"}
       : Expr
  
  Ederef_Evar uses section variable ty.
  Ederef_Enull = {e: *nullptr}
       : Expr
  
  Ederef_Enull uses section variable ty.
  Eaddrof_local_ref = {e: &$"Qux"}
       : Expr
  
  Eaddrof_local_ref uses section variable ty.
  Eaddrof_global_ref = {e: &$::"Qux"}
       : Expr
  
  Eaddrof_global_ref uses section variable ty.
  Eassign_1 = {e: $"pi" = #314}
       : Expr
  
  Eassign_1 uses section variable ty.
  Eassign_op_custom_Bshr = {e: $"foo" >>= #21}
       : Expr
  
  Eassign_op_custom_Bshr uses section variable ty.
  Eassign_op_default_Badd = {e: #42 += #314}
       : Expr
  
  Eassign_op_default_Badd uses section variable ty.
  Eassign_op_default_Band = {e: #42 &= #314}
       : Expr
  
  Eassign_op_default_Band uses section variable ty.
  Eassign_op_default_Bdiv = {e: #42 /= #314}
       : Expr
  
  Eassign_op_default_Bdiv uses section variable ty.
  Eassign_op_default_Bmul = {e: #42 *= #314}
       : Expr
  
  Eassign_op_default_Bmul uses section variable ty.
  Eassign_op_default_Bor = {e: #42 |= #314}
       : Expr
  
  Eassign_op_default_Bor uses section variable ty.
  Eassign_op_default_Bmod = {e: #42 %= #314}
       : Expr
  
  Eassign_op_default_Bmod uses section variable ty.
  Eassign_op_default_Bshl = {e: #42 <<= #314}
       : Expr
  
  Eassign_op_default_Bshl uses section variable ty.
  Eassign_op_default_Bsub = {e: #42 -= #314}
       : Expr
  
  Eassign_op_default_Bsub uses section variable ty.
  Eassign_op_default_Bxor = {e: #42 ^= #314}
       : Expr
  
  Eassign_op_default_Bxor uses section variable ty.
  Epreinc_1 = {e: ++{?: e}}
       : Expr
  
  Epreinc_1 uses section variables ty e.
  Epreinc_2 = {e: ++#41}
       : Expr
  
  Epreinc_2 uses section variable ty.
  Epostinc_1 = {e: {?: e}++}
       : Expr
  
  Epostinc_1 uses section variables ty e.
  Epostinc_2 = {e: #41++}
       : Expr
  
  Epostinc_2 uses section variable ty.
  Epredec_1 = {e: --{?: e}}
       : Expr
  
  Epredec_1 uses section variables ty e.
  Epredec_2 = {e: --#41}
       : Expr
  
  Epredec_2 uses section variable ty.
  Epostdec_1 = {e: {?: e}--}
       : Expr
  
  Epostdec_1 uses section variables ty e.
  Epostdec_2 = {e: #41--}
       : Expr
  
  Epostdec_2 uses section variable ty.
  Eseqand_1 = {e: (#true && #false)}
       : Expr
  Eseqand_2 = {e: (#true && (#false && #true))}
       : Expr
  Eseqor_1 = {e: (#true || #false)}
       : Expr
  Eseqor_2 = {e: (#true || (#false || #true))}
       : Expr
  Ecomma_1 = {e: {:comma:{?: e}, {?: e}:}}
       : Expr
  
  Ecomma_1 uses section variable e.
  Ecomma_2 = {e: {:comma:++$"baz", {?: e}:}}
       : Expr
  
  Ecomma_2 uses section variables ty e.
  Ecall_nil_1 = {e: {?: e}()}
       : Expr
  
  Ecall_nil_1 uses section variables ty e.
  Ecall_nil_2 = {e: $::"fn"()}
       : Expr
  
  Ecall_nil_2 uses section variable ty.
  Ecall_cons_nowrap_1 = {e: {?: e}(#42, #false)}
       : Expr
  
  Ecall_cons_nowrap_1 uses section variables ty e.
  Ecall_cons_nowrap_2 = {e: $::"fn"(#42, #false)}
       : Expr
  
  Ecall_cons_nowrap_2 uses section variable ty.
  Ecall_cons_wrap_1 =
  {e: {?: e}(#42,
             #false,
             STRING#to_chars
                      "FooBarBazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbaz")}
       : Expr
  
  Ecall_cons_wrap_1 uses section variables ty e.
  Ecall_cons_wrap_2 =
  {e: $::"fn"(#42,
              #false,
              STRING#to_chars
                       "FooBarBazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbaz")}
       : Expr
  
  Ecall_cons_wrap_2 uses section variable ty.
  Ecast_elide_1 =
  λ (cast : Cast) (vc : ValCat), {e: {?: e}}
       : Cast → ValCat → Expr
  
  Arguments Ecast_elide_1 cast vc
  Ecast_elide_1 uses section variables ty e.
  Ecast_elide_2 =
  λ (cast : Cast) (vc : ValCat), {e: #314}
       : Cast → ValCat → Expr
  
  Arguments Ecast_elide_2 cast vc
  Ecast_elide_2 uses section variable ty.
  Emember_1 = Emember {e: $"foo"} "bar" false ty
       : Expr
  
  Emember_1 uses section variable ty.
  Emember_call_nil_1 = {e: {?: e}."fn"()}
       : Expr
  
  Emember_call_nil_1 uses section variables ty e.
  Emember_call_nil_2 = {e: $::"foo"."fn"()}
       : Expr
  
  Emember_call_nil_2 uses section variable ty.
  Emember_call_cons_nowrap_1 = {e: {?: e}."fn"%bs(#42, #false)}
       : Expr
  
  Emember_call_cons_nowrap_1 uses section variables ty e.
  Emember_call_cons_nowrap_2 = {e: $::"foo"."fn"%bs(#42, #false)}
       : Expr
  
  Emember_call_cons_nowrap_2 uses section variable ty.
  Emember_call_cons_wrap_1 =
  {e: {?: e}."fn"%bs(#42,
                     #false,
                     STRING#to_chars
                              "FooBarBazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbaz")}
       : Expr
  
  Emember_call_cons_wrap_1 uses section variables ty e.
  Emember_call_cons_wrap_2 =
  {e: $::"foo"."fn"%bs(#42,
                       #false,
                       STRING#to_chars
                                "FooBarBazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbaz")}
       : Expr
  
  Emember_call_cons_wrap_2 uses section variable ty.
  Esubscript_1 = {e: {?: e}[#42]}
       : Expr
  
  Esubscript_1 uses section variables ty e.
  Esubscript_2 = {e: $"foo"[#314]}
       : Expr
  
  Esubscript_2 uses section variable ty.
  Esizeof_type_1 = {e: sizeof(ty: {?: ty})}
       : Expr
  
  Esizeof_type_1 uses section variable ty.
  Esizeof_type_2 = {e: sizeof(ty: ptr<uint8>)}
       : Expr
  
  Esizeof_type_2 uses section variable ty.
  Esizeof_type_3 = {e: sizeof(ty: "Foo")}
       : Expr
  
  Esizeof_type_3 uses section variable ty.
  Esizeof_Expr_1 = {e: sizeof(expr: {?: e})}
       : Expr
  
  Esizeof_Expr_1 uses section variables ty e.
  Esizeof_Expr_2 = {e: sizeof(expr: #314)}
       : Expr
  
  Esizeof_Expr_2 uses section variable ty.
  Esizeof_Expr_3 = {e: sizeof(expr: $"foo")}
       : Expr
  
  Esizeof_Expr_3 uses section variable ty.
  Ealignof_type_1 = {e: alignof(ty: {?: ty})}
       : Expr
  
  Ealignof_type_1 uses section variable ty.
  Ealignof_type_2 = {e: alignof(ty: ptr<uint8>)}
       : Expr
  
  Ealignof_type_2 uses section variable ty.
  Ealignof_type_3 = {e: alignof(ty: "Foo")}
       : Expr
  
  Ealignof_type_3 uses section variable ty.
  Ealignof_Expr_1 = {e: alignof(expr: {?: e})}
       : Expr
  
  Ealignof_Expr_1 uses section variables ty e.
  Ealignof_Expr_2 = {e: alignof(expr: #314)}
       : Expr
  
  Ealignof_Expr_2 uses section variable ty.
  Ealignof_Expr_3 = {e: alignof(expr: $"foo")}
       : Expr
  
  Ealignof_Expr_3 uses section variable ty.
  Eoffsetof_1 = {e: offsetof({?: "foo"},"bar")}
       : Expr
  
  Eoffsetof_1 uses section variable ty.
  Econstructor_nil = {e: #"Foo"()}
       : Expr
  
  Econstructor_nil uses section variable ty.
  Econstructor_cons_nowrap = {e: #"Foo"(#42, #false)}
       : Expr
  
  Econstructor_cons_nowrap uses section variable ty.
  Econstructor_cons_wrap =
  {e: #"Qux::Zop"(#42,
                  #false,
                  STRING#to_chars
                           "FooBarBazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbaz")}
       : Expr
  
  Econstructor_cons_wrap uses section variable ty.
  Eimplicit_1 = {e: {?: e}}
       : Expr
  
  Eimplicit_1 uses section variable e.
  Eimplicit_2 = {e: #"Foo"()}
       : Expr
  
  Eimplicit_2 uses section variable ty.
  Eimplicit_init_1 = {e: {?: ty}{{VALUE INIT}}}
       : Expr
  
  Eimplicit_init_1 uses section variable ty.
  Eimplicit_init_2 = {e: uint8{{VALUE INIT}}}
       : Expr
  Eif_1 = {e: #true ? $"fn"() : $"foo" *= $"bar"}
       : Expr
  
  Eif_1 uses section variable ty.
  {e: this}
       : Expr
  {e: nullptr}
       : Expr
  Einitlist_nil_1 = {e: ({?: ty}){}}
       : Expr
  
  Einitlist_nil_1 uses section variable ty.
  Einitlist_nil_2 = {e: (uint64){}}
       : Expr
  Einitlist_cons_no_wrap_no_default_1 = {e: ({?: ty}){#42, #false}}
       : Expr
  
  Einitlist_cons_no_wrap_no_default_1 uses section variable ty.
  Einitlist_cons_no_wrap_no_default_2 = {e: (uint64){#42, #false}}
       : Expr
  
  Einitlist_cons_no_wrap_no_default_2 uses section variable ty.
  Einitlist_cons_wrap_no_default_1 =
  {e: ({?: ty}){#42,
                #false,
                STRING#to_chars
                         "FooBarBazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbaz"}}
       : Expr
  
  Einitlist_cons_wrap_no_default_1 uses section variable ty.
  Einitlist_cons_wrap_no_default_2 =
  {e: (uint64){#42,
               #false,
               STRING#to_chars
                        "FooBarBazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbaz"}}
       : Expr
  
  Einitlist_cons_wrap_no_default_2 uses section variable ty.
  Einitlist_cons_no_wrap_default_1 =
  {e: ({?: ty}){#42, #false}{default: #314}}
       : Expr
  
  Einitlist_cons_no_wrap_default_1 uses section variable ty.
  Einitlist_cons_no_wrap_default_2 =
  {e: (uint64){#42, #false}{default: #314}}
       : Expr
  
  Einitlist_cons_no_wrap_default_2 uses section variable ty.
  Einitlist_cons_wrap_default_1 =
  {e: ({?: ty}){#42,
                #false,
                STRING#to_chars
                         "FooBarBazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbaz"}{default:
      #314}}
       : Expr
  
  Einitlist_cons_wrap_default_1 uses section variable ty.
  Einitlist_cons_wrap_default_2 =
  {e: (uint64){#42,
               #false,
               STRING#to_chars
                        "FooBarBazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbazfoobarbaz"}{default:
      #314}}
       : Expr
  
  Einitlist_cons_wrap_default_2 uses section variable ty.
  Enew_nonarray_nil_1 = {e: new {?: ty}}
       : Expr
  
  Enew_nonarray_nil_1 uses section variables ty e.
  Enew_nonarray_nil_2 = {e: new uint8}
       : Expr
  
  Enew_nonarray_nil_2 uses section variable ty.
  Enew_nonarray_cons_1 = {e: new (#42, #false) {?: ty}}
       : Expr
  
  Enew_nonarray_cons_1 uses section variables ty e.
  Enew_nonarray_cons_2 = {e: new (#42, #false) "Foo"}
       : Expr
  
  Enew_nonarray_cons_2 uses section variable ty.
  Enew_array_nil_1 = {e: new {?: ty}[#314]}
       : Expr
  
  Enew_array_nil_1 uses section variables ty e.
  Enew_array_nil_2 = {e: new uint8[#314]}
       : Expr
  
  Enew_array_nil_2 uses section variable ty.
  Edelete_nonarray_1 = {e: delete {?: e}}
       : Expr
  
  Edelete_nonarray_1 uses section variables ty e.
  Edelete_nonarray_2 = {e: delete $"foo"}
       : Expr
  
  Edelete_nonarray_2 uses section variable ty.
  Edelete_array_1 = {e: delete[] {?: e}}
       : Expr
  
  Edelete_array_1 uses section variables ty e.
  Edelete_array_2 = {e: delete[] $"foo"}
       : Expr
  
  Edelete_array_2 uses section variable ty.
  Eandclean_1 = {e: {?: e}}
       : Expr
  
  Eandclean_1 uses section variable e.
  Eandclean_2 = {e: $"foo"}
       : Expr
  
  Eandclean_2 uses section variable ty.
  Ematerialize_temp_1 = {e: {?: e}}
       : Expr
  
  Ematerialize_temp_1 uses section variable e.
  Ematerialize_temp_2 = {e: $"foo"}
       : Expr
  
  Ematerialize_temp_2 uses section variable ty.
  {e: __builtin_alloca}
       : BuiltinFn
  {e: __builtin_alloca_with_align}
       : BuiltinFn
  {e: __builtin_launder}
       : BuiltinFn
  {e: __builtin_expect}
       : BuiltinFn
  {e: __builtin_unreachable}
       : BuiltinFn
  {e: __builtin_trap}
       : BuiltinFn
  {e: __builtin_bswap16}
       : BuiltinFn
  {e: __builtin_bswap32}
       : BuiltinFn
  {e: __builtin_bswap64}
       : BuiltinFn
  {e: __builtin_bswap128}
       : BuiltinFn
  {e: __builtin_bzero}
       : BuiltinFn
  {e: __builtin_ffs}
       : BuiltinFn
  {e: __builtin_ffsl}
       : BuiltinFn
  {e: __builtin_ffsll}
       : BuiltinFn
  {e: __builtin_clz}
       : BuiltinFn
  {e: __builtin_clzl}
       : BuiltinFn
  {e: __builtin_clzll}
       : BuiltinFn
  {e: __builtin_ctz}
       : BuiltinFn
  {e: __builtin_ctzl}
       : BuiltinFn
  {e: __builtin_ctzll}
       : BuiltinFn
  {e: __builtin_popcount}
       : BuiltinFn
  {e: __builtin_popcountl}
       : BuiltinFn
  {e: __builtin_UNKNOWN_"__builtin__foobarbaz"}
       : BuiltinFn
  Eva_arg_1 = {e: __builtin_vaarg({?: e}, {?: ty})}
       : Expr
  
  Eva_arg_1 uses section variables ty e.
  Eva_arg_2 = {e: __builtin_vaarg(#217, {?: ty})}
       : Expr
  
  Eva_arg_2 uses section variable ty.
  Epseudo_destructor_1 = {e: {?: e}->~{?: ty}()}
       : Expr
  
  Epseudo_destructor_1 uses section variables ty e.
  Epseudo_destructor_2 = {e: #217.~{?: ty}()}
       : Expr
  
  Epseudo_destructor_2 uses section variable ty.
  {e: {UNSUPPORTED: "This was an unsupported operation"}}
       : Expr
