  $ . ../setup-project.sh
  $ dune build test.vo
  Notation_Tptr_1 = "bool*"%cpp_type
       : type
  Notation_Tptr_2 = {t: ptr<{?: ty}>}
       : type
  
  Notation_Tptr_2 uses section variable ty.
  Notation_Tref_1 = "bool&"%cpp_type
       : type
  Notation_Tref_2 = {t: ref&<{?: ty}>}
       : type
  
  Notation_Tref_2 uses section variable ty.
  Notation_Trv_ref_1 = "bool&&"%cpp_type
       : type
  Notation_Trv_ref_2 = {t: ref&&<{?: ty}>}
       : type
  
  Notation_Trv_ref_2 uses section variable ty.
  Notation_Tref_Trv_ref = {t: ref&<ref&&<{?: ty}>>}
       : type
  
  Notation_Tref_Trv_ref uses section variable ty.
  Notation_Trv_ref_Tref = {t: ref&&<ref&<{?: ty}>>}
       : type
  
  Notation_Trv_ref_Tref uses section variable ty.
  Notation_void = "void"%cpp_type
       : type
  Notation_Tarray_1 = "nullptr_t[100]"%cpp_type
       : type
  Notation_Tarray_2 = {t: {?: ty}[n]}
       : type
  
  Notation_Tarray_2 uses section variables ty n.
  Notation_Tnamed_1 = "foobarbaz"%cpp_type
       : type
  Notation_Tnamed_2 = {t: nm}
       : type
  
  Notation_Tnamed_2 uses section variable nm.
  Notation_Tfunction_novariadic_noargs_1 = "void()"%cpp_type
       : type
  Notation_Tfunction_novariadic_noargs_2 =
  {t: extern CC_C ???() -> {?: rty}}
       : type
  
  Notation_Tfunction_novariadic_noargs_2 uses section variable rty.
  Notation_Tfunction_novariadic_args_nowrap_1 =
  "void(bool, nullptr_t)"%cpp_type
       : type
  Notation_Tfunction_novariadic_args_nowrap_2 =
  {t: extern CC_C ???({?: aty1}, {?: "void"%cpp_type}, {?: aty2}) -> {?: rty}}
       : type
  
  Notation_Tfunction_novariadic_args_nowrap_2 uses section variables
  rty aty1 aty2.
  Notation_Tfunction_novariadic_args_wrap =
  "void(askldjfo;lasjdlkfj;aklsdjg;blkajl;ksdjfl;aksdjf;lkasjdf;lkajsd;lfkjas;dlkfj;alskdjf;kalsdjf;lk, askldjflk;ajsdkl;gjasdklgjakl;sdjgl;kasdjfl;kjasdlfhajklsdgljkasdhfgjkahsdfljk)"%cpp_type
       : type
  Notation_Tfunction_variadic_noargs_1 = "void(...)"%cpp_type
       : type
  Notation_Tfunction_variadic_noargs_2 =
  {t: extern CC_C ???()(...) -> {?: rty}}
       : type
  
  Notation_Tfunction_variadic_noargs_2 uses section variable rty.
  Notation_Tfunction_variadic_args_nowrap_1 =
  "void(bool, nullptr_t, ...)"%cpp_type
       : type
  Notation_Tfunction_variadic_args_nowrap_2 =
  {t: extern CC_C ???({?: aty1}, {?: "void"%cpp_type}, {?: aty2})(...) -> 
      {?: rty}}
       : type
  
  Notation_Tfunction_variadic_args_nowrap_2 uses section variables
  rty aty1 aty2.
  Notation_Tfunction_variadic_args_wrap =
  "void(askldjfo;lasjdlkfj;aklsdjg;blkajl;ksdjfl;aksdjf;lkasjdf;lkajsd;lfkjas;dlkfj;alskdjf;kalsdjf;lk, askldjflk;ajsdkl;gjasdklgjakl;sdjgl;kasdjfl;kjasdlfhajklsdgljkasdhfgjkahsdfljk, ...)"%cpp_type
       : type
  Notation_Tbool = "bool"%cpp_type
       : type
  Notation_Tmember_pointer_1 = "char foobarbaz::*"%cpp_type
       : type
  Notation_mut_1 = {t: mut {?: "bool"}}
       : type
  Notation_mut_2 = {t: mut mut {?: "bool"}}
       : type
  Notation_const_1 = "const bool"%cpp_type
       : type
  Notation_const_2 = "const void* const"%cpp_type
       : type
  Notation_volatile_1 = "volatile bool"%cpp_type
       : type
  Notation_volatile_2 = "const void* volatile"%cpp_type
       : type
  Notation_const_volatile_1 = "const volatile bool"%cpp_type
       : type
  Notation_const_volatile_2 =
  "const volatile void* const volatile"%cpp_type
       : type
