  $ . ../setup-project.sh
  $ dune build test.vo
  "~~~TESTING COMPACT NOTATIONS~~~"%pstring
       : PrimString.string
  NOTATION_wp_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' this : ptr) 
    (K : Kpred),
    ::wpS
      [region: "bar" @ p'; "foo" @ p; [this := this]; return {?: "void*"}]
      {s: ($"foo" + $"bar");
          break;
          continue;
          ($"foo" + $"bar");
          ($"foo" + $"bar");
          return;
          return ($"foo" + $"bar");
          // end block}
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → translation_unit → ptr → ptr → ptr → Kpred → mpred
  
  Arguments NOTATION_wp_nowrap ti _Σ Σ σ tu p p' this K%_bi_scope
  NOTATION_wp_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' p'' p''' this : ptr) 
    (K : Kpred),
    ::wpS
      [region:
        "qux" @ p'''; "baz" @ p''; "bar" @ p'; "foo" @ p; 
        [this := this]; return {?: "void*"}]
      {s: ($"foo" + $"bar");
          break;
          continue;
          ($"foo" + $"bar");
          ($"foo" + $"bar");
          return;
          return ($"foo" + $"bar");
          // end block
          ($"foo" + $"bar");
          break;
          continue;
          ($"foo" + $"bar");
          ($"foo" + $"bar");
          return;
          return ($"foo" + $"bar");
          // end block
          ($"foo" + $"bar");
          break;
          continue;
          ($"foo" + $"bar");
          ($"foo" + $"bar");
          return;
          return ($"foo" + $"bar");
          // end block
          ($"foo" + $"bar");
          break;
          continue;
          ($"foo" + $"bar");
          ($"foo" + $"bar");
          return;
          return ($"foo" + $"bar");
          // end block
          // end block}
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit → ptr → ptr → ptr → ptr → ptr → Kpred → mpred
  
  Arguments NOTATION_wp_wrap ti _Σ Σ σ tu p p' p'' p''' this K%_bi_scope
  NOTATION_wp_decl_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' this : ptr) 
    (decl : VarDecl) (Q : region → FreeTemps → epred),
    ::wpD
      [region: "bar" @ p'; "foo" @ p; [this := this]; return {?: "void*"}] decl
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr → ptr → ptr → VarDecl → (region → FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_decl_nowrap ti _Σ Σ σ tu p p' 
    this decl%_CPP_stmt_scope Q%_function_scope
  NOTATION_wp_atomic_nil =
  λ (ti : biIndex) (_Σ : gFunctors) (σ : genv) (M : coPset) (Q : val → mpred),
    ::wpAtomic (Mask ↦ M; Type ↦ {?: "void*"}) {e: "__atomic_load"()}
       : ∀ (ti : biIndex) (_Σ : gFunctors),
           genv → coPset → (val → mpred) → mpred
  
  Arguments NOTATION_wp_atomic_nil ti _Σ σ M Q%_function_scope
  NOTATION_wp_atomic_cons_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (σ : genv) (M : coPset) (Q : val → mpred),
    ::wpAtomic
      (Mask ↦ M; Type ↦ {?: "void*"}) 
      {e: "__atomic_load"(Vundef, Vundef, Vundef)}
       : ∀ (ti : biIndex) (_Σ : gFunctors),
           genv → coPset → (val → mpred) → mpred
  
  Arguments NOTATION_wp_atomic_cons_nowrap ti _Σ σ M Q%_function_scope
  NOTATION_wp_atomic_cons_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (σ : genv) (M : coPset) (Q : val → mpred),
    ::wpAtomic
      (Mask ↦ M; Type ↦ {?: "void*"}) 
      {e: "__atomic_load"(Vundef,
                          Vundef,
                          Vundef,
                          Vundef,
                          Vundef,
                          Vundef,
                          Vundef,
                          1123784018923740981723509817230984710298374098123740981723490817230984710293840891273489012734089%Z)}
       : ∀ (ti : biIndex) (_Σ : gFunctors),
           genv → coPset → (val → mpred) → mpred
  
  Arguments NOTATION_wp_atomic_cons_wrap ti _Σ σ M Q%_function_scope
  NOTATION_wp_builtin_nil =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (Q : val → epred),
    ::wpBuiltin (Type ↦ {?: "void*"}) {e: "__builtin_popcount"()}
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → (val → epred) → mpred
  
  Arguments NOTATION_wp_builtin_nil ti _Σ Σ σ Q%_function_scope
  NOTATION_wp_builtin_cons_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (Q : val → epred),
    ::wpBuiltin
      (Type ↦ {?: "void*"}) {e: "__builtin_popcount"(Vundef, Vundef, Vundef)}
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → (val → epred) → mpred
  
  Arguments NOTATION_wp_builtin_cons_nowrap ti _Σ Σ σ Q%_function_scope
  NOTATION_wp_builtin_cons_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (Q : val → epred),
    ::wpBuiltin
      (Type ↦ {?: "void*"}) 
      {e: "__builtin_popcount"(Vundef,
                               Vundef,
                               Vundef,
                               Vundef,
                               Vundef,
                               Vundef,
                               Vundef,
                               1123784018923740981723509817230984710298374098123740981723490817230984710293840891273489012734089%Z)}
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → (val → epred) → mpred
  
  Arguments NOTATION_wp_builtin_cons_wrap ti _Σ Σ σ Q%_function_scope
  NOTATION_wp_destroy_val_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p : ptr) (E : epred),
    ::destroy_val {pointer: p; qualifiers: const; type: {?: "void*"}}
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → translation_unit → ptr → epred → mpred
  
  Arguments NOTATION_wp_destroy_val_nowrap ti _Σ Σ σ tu p E%_bi_scope
  NOTATION_wp_destroy_val_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (E : epred) (aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : ptr),
    ::destroy_val
      {pointer: aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa;
          qualifiers: const;
          type: {?: "void*"}}
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → translation_unit → epred → ptr → mpred
  
  Arguments NOTATION_wp_destroy_val_wrap ti _Σ Σ σ tu 
    E%_bi_scope
    aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  NOTATION_destroy_val_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p : ptr) (E : epred),
    ::destroy_val {pointer: p; type: {?: "void*"}}
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → translation_unit → ptr → epred → mpred
  
  Arguments NOTATION_destroy_val_nowrap ti _Σ Σ σ tu p E%_bi_scope
  NOTATION_destroy_val_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (E : epred) (aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : ptr),
    ::destroy_val
      {pointer: aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa;
          type: {?: "void*"}}
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → translation_unit → epred → ptr → mpred
  
  Arguments NOTATION_destroy_val_wrap ti _Σ Σ σ tu E%_bi_scope
    aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  NOTATION_interp_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (free : FreeTemps) 
    (E : epred), ::interp { free }
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → translation_unit → FreeTemps → epred → mpred
  
  Arguments NOTATION_interp_nowrap ti _Σ Σ σ tu free%_free_scope E%_bi_scope
  NOTATION_interp_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (E : epred),
    ::interp
      { (((((((((1 |*| 1) |*| 1) |*| 1) |*| 1) |*| 1) |*| 1) |*| 1) |*| 1)
         |*| 1)
        |*| 1 }
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → translation_unit → epred → mpred
  
  Arguments NOTATION_interp_wrap ti _Σ Σ σ tu E%_bi_scope
  NOTATION_wp_lval_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' this : ptr) 
    (Q : ptr → FreeTemps → epred),
    ::wpL
      [region: "bar" @ p'; "foo" @ p; [this := this]; return {?: "void*"}]
      {e: ($"foo" + $"bar")}
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr → ptr → ptr → (ptr → FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_lval_nowrap ti _Σ Σ σ tu p p' this Q%_function_scope
  NOTATION_wp_lval_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' p'' p''' this : ptr) 
    (Q : ptr → FreeTemps → epred),
    ::wpL
      [region:
        "qux" @ p'''; "baz" @ p''; "bar" @ p'; "foo" @ p; 
        [this := this]; return {?: "void*"}]
      {e: ($"foo" + $"bar")}
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr → ptr → ptr → ptr → ptr → (ptr → FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_lval_wrap ti _Σ Σ σ tu p p' 
    p'' p''' this Q%_function_scope
  NOTATION_wp_init_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' this : ptr) 
    (Q : FreeTemps → epred),
    ::wpPRᵢ
      [region: "bar" @ p'; "foo" @ p; [this := this]; return {?: "void*"}]
      (Pointer ↦ this) 
      {e: ($"foo" + $"bar")}
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit → ptr → ptr → ptr → (FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_init_nowrap ti _Σ Σ σ tu p p' this Q%_function_scope
  NOTATION_wp_init_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' p'' p''' this : ptr) 
    (Q : FreeTemps → epred),
    ::wpPRᵢ
      [region:
        "qux" @ p'''; "baz" @ p''; "bar" @ p'; "foo" @ p; 
        [this := this]; return {?: "void*"}]
      (Pointer ↦ this) 
      {e: ($"foo" + $"bar")}
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr → ptr → ptr → ptr → ptr → (FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_init_wrap ti _Σ Σ σ tu p p' 
    p'' p''' this Q%_function_scope
  NOTATION_wp_prval_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' this : ptr) 
    (Q : ptr → FreeTemps → epred),
    ::wpPR
      [region: "bar" @ p'; "foo" @ p; [this := this]; return {?: "void*"}]
      {e: ($"foo" + $"bar")}
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr → ptr → ptr → (ptr → FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_prval_nowrap ti _Σ Σ σ tu p p' this Q%_function_scope
  NOTATION_wp_prval_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' p'' p''' this : ptr) 
    (Q : ptr → FreeTemps → epred),
    ::wpPR
      [region:
        "qux" @ p'''; "baz" @ p''; "bar" @ p'; "foo" @ p; 
        [this := this]; return {?: "void*"}]
      {e: ($"foo" + $"bar")}
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr → ptr → ptr → ptr → ptr → (ptr → FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_prval_wrap ti _Σ Σ σ tu p p' 
    p'' p''' this Q%_function_scope
  NOTATION_wp_operand_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' this : ptr) 
    (Q : val → FreeTemps → epred),
    ::wpOperand
      [region: "bar" @ p'; "foo" @ p; [this := this]; return {?: "void*"}]
      {e: ($"foo" + $"bar")}
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr → ptr → ptr → (val → FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_operand_nowrap ti _Σ Σ σ tu p p' this Q%_function_scope
  NOTATION_wp_operand_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' p'' p''' this : ptr) 
    (Q : val → FreeTemps → epred),
    ::wpOperand
      [region:
        "qux" @ p'''; "baz" @ p''; "bar" @ p'; "foo" @ p; 
        [this := this]; return {?: "void*"}]
      {e: ($"foo" + $"bar")}
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr → ptr → ptr → ptr → ptr → (val → FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_operand_wrap ti _Σ Σ σ tu p 
    p' p'' p''' this Q%_function_scope
  NOTATION_wp_xval_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' this : ptr) 
    (Q : ptr → FreeTemps → epred),
    ::wpX
      [region: "bar" @ p'; "foo" @ p; [this := this]; return {?: "void*"}]
      {e: ($"foo" + $"bar")}
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr → ptr → ptr → (ptr → FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_xval_nowrap ti _Σ Σ σ tu p p' this Q%_function_scope
  NOTATION_wp_xval_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' p'' p''' this : ptr) 
    (Q : ptr → FreeTemps → epred),
    ::wpX
      [region:
        "qux" @ p'''; "baz" @ p''; "bar" @ p'; "foo" @ p; 
        [this := this]; return {?: "void*"}]
      {e: ($"foo" + $"bar")}
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr → ptr → ptr → ptr → ptr → (ptr → FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_xval_wrap ti _Σ Σ σ tu p p' 
    p'' p''' this Q%_function_scope
  NOTATION_wp_glval_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' this : ptr) 
    (Q : ptr → FreeTemps → epred),
    ::wpGL
      [region: "bar" @ p'; "foo" @ p; [this := this]; return {?: "void*"}]
      {e: ($"foo" + $"bar")}
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr → ptr → ptr → (ptr → FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_glval_nowrap ti _Σ Σ σ tu p p' this Q%_function_scope
  NOTATION_wp_glval_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' p'' p''' this : ptr) 
    (Q : ptr → FreeTemps → epred),
    ::wpGL
      [region:
        "qux" @ p'''; "baz" @ p''; "bar" @ p'; "foo" @ p; 
        [this := this]; return {?: "void*"}]
      {e: ($"foo" + $"bar")}
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr → ptr → ptr → ptr → ptr → (ptr → FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_glval_wrap ti _Σ Σ σ tu p p' 
    p'' p''' this Q%_function_scope
  NOTATION_wp_discard_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p this : ptr) 
    (Q : FreeTemps → mpred),
    ::wpGLₓ
      [region: "foo" @ p; [this := this]; return {?: "void*"}]
      {e: ($"foo" + $"bar")}
       : ∀ (ti : biIndex) (_Σ : gFunctors),
           cpp_logic ti _Σ
           → genv → translation_unit → ptr → ptr → (FreeTemps → mpred) → mpred
  
  Arguments NOTATION_wp_discard_nowrap ti _Σ Σ σ tu p this Q%_function_scope
  NOTATION_wp_discard_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p this : ptr) 
    (Q : FreeTemps → mpred),
    ::wpGLₓ
      [region: "foo" @ p; [this := this]; return {?: "void*"}]
      {e: ($"foo" + $"bar")}
       : ∀ (ti : biIndex) (_Σ : gFunctors),
           cpp_logic ti _Σ
           → genv → translation_unit → ptr → ptr → (FreeTemps → mpred) → mpred
  
  Arguments NOTATION_wp_discard_nowrap ti _Σ Σ σ tu p this Q%_function_scope
  NOTATION_wp_func =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (F : Func) (ls : list ptr) 
    (Q : ptr → epred), ::wpFunc Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → translation_unit → Func → list ptr → (ptr → epred) → mpred
  
  Arguments NOTATION_wp_func ti _Σ Σ σ tu F ls%_list_scope Q%_function_scope
  NOTATION_wp_method =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (M : Method) 
    (ls : list ptr) (Q : ptr → epred), ::wpMethod Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → translation_unit → Method → list ptr → (ptr → epred) → mpred
  
  Arguments NOTATION_wp_method ti _Σ Σ σ tu M ls%_list_scope Q%_function_scope
  NOTATION_wp_ctor =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (C : Ctor) (ls : list ptr) 
    (Q : ptr → epred), ::wpCtor Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → translation_unit → Ctor → list ptr → (ptr → epred) → mpred
  
  Arguments NOTATION_wp_ctor ti _Σ Σ σ tu C ls%_list_scope Q%_function_scope
  NOTATION_wp_dtor =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (D : Dtor) (ls : list ptr) 
    (Q : ptr → epred), ::wpDtor Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → translation_unit → Dtor → list ptr → (ptr → epred) → mpred
  
  Arguments NOTATION_wp_dtor ti _Σ Σ σ tu D ls%_list_scope Q%_function_scope
  NOTATION_wp_args_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' this : ptr) 
    (tys_ar : evaluation_order.t) (es : list (wp.WPE.M ptr)) 
    (Q : list decltype * function_arity),
    ::wpArgs
      [region: "bar" @ p'; "foo" @ p; [this := this]; return {?: "void*"}]
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr
               → ptr
                 → ptr
                   → evaluation_order.t
                     → list (wp.WPE.M ptr)
                       → list decltype * function_arity
                         → list Expr
                           → (list ptr
                              → list ptr → FreeTemps → FreeTemps → mpred)
                             → mpred
  
  Arguments NOTATION_wp_args_nowrap ti _Σ Σ σ tu p p' 
    this tys_ar es%_list_scope Q es%_list_scope Q%_function_scope
  NOTATION_wp_args_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' p'' p''' this : ptr) 
    (tys_ar : evaluation_order.t) (es : list (wp.WPE.M ptr)) 
    (Q : list decltype * function_arity),
    ::wpArgs
      [region:
        "qux" @ p'''; "baz" @ p''; "bar" @ p'; "foo" @ p; 
        [this := this]; return {?: "void*"}]
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr
               → ptr
                 → ptr
                   → ptr
                     → ptr
                       → evaluation_order.t
                         → list (wp.WPE.M ptr)
                           → list decltype * function_arity
                             → list Expr
                               → (list ptr
                                  → list ptr → FreeTemps → FreeTemps → mpred)
                                 → mpred
  
  Arguments NOTATION_wp_args_wrap ti _Σ Σ σ tu p p' 
    p'' p''' this tys_ar es%_list_scope Q es%_list_scope 
    Q%_function_scope
  NOTATION_wp_initialize_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p this : ptr) 
    (Q : FreeTemps → epred),
    ::wpInitialize
      [region: "foo" @ p; [this := this]; return {?: "void*"}]
      (p |-> type_ptrR {?: "void*"})
      {e: ($"foo" + $"bar")}
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → translation_unit → ptr → ptr → (FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_initialize_nowrap ti _Σ Σ σ tu p this Q%_function_scope
  NOTATION_wp_initialize_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' p'' p''' this : ptr) 
    (Q : FreeTemps → epred),
    ::wpInitialize
      [region:
        "qux" @ p'''; "baz" @ p''; "bar" @ p'; "foo" @ p; 
        [this := this]; return {?: "void*"}]
      (p |-> type_ptrR {?: "void*"})
      {e: ($"foo" + $"bar")}
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr → ptr → ptr → ptr → ptr → (FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_initialize_wrap ti _Σ Σ σ tu 
    p p' p'' p''' this Q%_function_scope
  "~~~TESTING Verbose NOTATIONS~~~"%pstring
       : PrimString.string
  NOTATION_wp_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' this : ptr) 
    (K : Kpred),
    ::wpS
      [region: "bar" @ p'; "foo" @ p; [this := this]; return {?: "void*"}]
      {s: ($"foo" + $"bar");
          break;
          continue;
          ($"foo" + $"bar");
          ($"foo" + $"bar");
          return;
          return ($"foo" + $"bar");
          // end block}
      K
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → translation_unit → ptr → ptr → ptr → Kpred → mpred
  
  Arguments NOTATION_wp_nowrap ti _Σ Σ σ tu p p' this K%_bi_scope
  NOTATION_wp_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' p'' p''' this : ptr) 
    (K : Kpred),
    ::wpS
      [region:
        "qux" @ p'''; "baz" @ p''; "bar" @ p'; "foo" @ p; 
        [this := this]; return {?: "void*"}]
      {s: ($"foo" + $"bar");
          break;
          continue;
          ($"foo" + $"bar");
          ($"foo" + $"bar");
          return;
          return ($"foo" + $"bar");
          // end block
          ($"foo" + $"bar");
          break;
          continue;
          ($"foo" + $"bar");
          ($"foo" + $"bar");
          return;
          return ($"foo" + $"bar");
          // end block
          ($"foo" + $"bar");
          break;
          continue;
          ($"foo" + $"bar");
          ($"foo" + $"bar");
          return;
          return ($"foo" + $"bar");
          // end block
          ($"foo" + $"bar");
          break;
          continue;
          ($"foo" + $"bar");
          ($"foo" + $"bar");
          return;
          return ($"foo" + $"bar");
          // end block
          // end block}
      K
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit → ptr → ptr → ptr → ptr → ptr → Kpred → mpred
  
  Arguments NOTATION_wp_wrap ti _Σ Σ σ tu p p' p'' p''' this K%_bi_scope
  NOTATION_wp_decl_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' this : ptr) 
    (decl : VarDecl) (Q : region → FreeTemps → epred),
    ::wpD
      [region: "bar" @ p'; "foo" @ p; [this := this]; return {?: "void*"}] decl
      Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr → ptr → ptr → VarDecl → (region → FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_decl_nowrap ti _Σ Σ σ tu p p' 
    this decl%_CPP_stmt_scope Q%_function_scope
  NOTATION_wp_atomic_nil =
  λ (ti : biIndex) (_Σ : gFunctors) (σ : genv) (M : coPset) (Q : val → mpred),
    ::wpAtomic (Mask ↦ M; Type ↦ {?: "void*"})  {e: "__atomic_load"()} Q
       : ∀ (ti : biIndex) (_Σ : gFunctors),
           genv → coPset → (val → mpred) → mpred
  
  Arguments NOTATION_wp_atomic_nil ti _Σ σ M Q%_function_scope
  NOTATION_wp_atomic_cons_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (σ : genv) (M : coPset) (Q : val → mpred),
    ::wpAtomic
      (Mask ↦ M; Type ↦ {?: "void*"}) 
       {e: "__atomic_load"(Vundef, Vundef, Vundef)}
      Q
       : ∀ (ti : biIndex) (_Σ : gFunctors),
           genv → coPset → (val → mpred) → mpred
  
  Arguments NOTATION_wp_atomic_cons_nowrap ti _Σ σ M Q%_function_scope
  NOTATION_wp_atomic_cons_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (σ : genv) (M : coPset) (Q : val → mpred),
    ::wpAtomic
      (Mask ↦ M; Type ↦ {?: "void*"}) 
       {e: "__atomic_load"(Vundef,
                           Vundef,
                           Vundef,
                           Vundef,
                           Vundef,
                           Vundef,
                           Vundef,
                           1123784018923740981723509817230984710298374098123740981723490817230984710293840891273489012734089%Z)}
      Q
       : ∀ (ti : biIndex) (_Σ : gFunctors),
           genv → coPset → (val → mpred) → mpred
  
  Arguments NOTATION_wp_atomic_cons_wrap ti _Σ σ M Q%_function_scope
  NOTATION_wp_builtin_nil =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (Q : val → epred),
    ::wpBuiltin (Type ↦ {?: "void*"}) {e: "__builtin_popcount"%pstring()} Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → (val → epred) → mpred
  
  Arguments NOTATION_wp_builtin_nil ti _Σ Σ σ Q%_function_scope
  NOTATION_wp_builtin_cons_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (Q : val → epred),
    ::wpBuiltin
      (Type ↦ {?: "void*"}) 
      {e: "__builtin_popcount"%pstring(Vundef, Vundef, Vundef)}
      Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → (val → epred) → mpred
  
  Arguments NOTATION_wp_builtin_cons_nowrap ti _Σ Σ σ Q%_function_scope
  NOTATION_wp_builtin_cons_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (Q : val → epred),
    ::wpBuiltin
      (Type ↦ {?: "void*"}) 
      {e: "__builtin_popcount"%pstring(Vundef,
                                       Vundef,
                                       Vundef,
                                       Vundef,
                                       Vundef,
                                       Vundef,
                                       Vundef,
                                       1123784018923740981723509817230984710298374098123740981723490817230984710293840891273489012734089%Z)}
      Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → (val → epred) → mpred
  
  Arguments NOTATION_wp_builtin_cons_wrap ti _Σ Σ σ Q%_function_scope
  NOTATION_destroy_val_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p : ptr) (E : epred),
    ::destroy_val {pointer: p; type: {?: "void*"}} E
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → translation_unit → ptr → epred → mpred
  
  Arguments NOTATION_destroy_val_nowrap ti _Σ Σ σ tu p E%_bi_scope
  NOTATION_destroy_val_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (E : epred) (aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa : ptr),
    ::destroy_val
      {pointer: aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa;
          type: {?: "void*"}}
      E
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → translation_unit → epred → ptr → mpred
  
  Arguments NOTATION_destroy_val_wrap ti _Σ Σ σ tu E%_bi_scope
    aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  NOTATION_interp_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (free : FreeTemps) 
    (E : epred), ::interp { free }  E
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → translation_unit → FreeTemps → epred → mpred
  
  Arguments NOTATION_interp_nowrap ti _Σ Σ σ tu free%_free_scope E%_bi_scope
  NOTATION_interp_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (E : epred),
    ::interp
      { (((((((((1 |*| 1) |*| 1) |*| 1) |*| 1) |*| 1) |*| 1) |*| 1) |*| 1)
         |*| 1)
        |*| 1 }
      E
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → translation_unit → epred → mpred
  
  Arguments NOTATION_interp_wrap ti _Σ Σ σ tu E%_bi_scope
  NOTATION_wp_lval_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' this : ptr) 
    (Q : ptr → FreeTemps → epred),
    ::wpL
      [region: "bar" @ p'; "foo" @ p; [this := this]; return {?: "void*"}]
      {e: ($"foo" + $"bar")}
      Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr → ptr → ptr → (ptr → FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_lval_nowrap ti _Σ Σ σ tu p p' this Q%_function_scope
  NOTATION_wp_lval_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' p'' p''' this : ptr) 
    (Q : ptr → FreeTemps → epred),
    ::wpL
      [region:
        "qux" @ p'''; "baz" @ p''; "bar" @ p'; "foo" @ p; 
        [this := this]; return {?: "void*"}]
      {e: ($"foo" + $"bar")}
      Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr → ptr → ptr → ptr → ptr → (ptr → FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_lval_wrap ti _Σ Σ σ tu p p' 
    p'' p''' this Q%_function_scope
  NOTATION_wp_init_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' this : ptr) 
    (Q : FreeTemps → epred),
    ::wpPRᵢ
      [region: "bar" @ p'; "foo" @ p; [this := this]; return {?: "void*"}]
      (Pointer ↦ this) 
      {e: ($"foo" + $"bar")}
      Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit → ptr → ptr → ptr → (FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_init_nowrap ti _Σ Σ σ tu p p' this Q%_function_scope
  NOTATION_wp_init_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' p'' p''' this : ptr) 
    (Q : FreeTemps → epred),
    ::wpPRᵢ
      [region:
        "qux" @ p'''; "baz" @ p''; "bar" @ p'; "foo" @ p; 
        [this := this]; return {?: "void*"}]
      (Pointer ↦ this) 
      {e: ($"foo" + $"bar")}
      Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr → ptr → ptr → ptr → ptr → (FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_init_wrap ti _Σ Σ σ tu p p' 
    p'' p''' this Q%_function_scope
  NOTATION_wp_prval_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' this : ptr) 
    (Q : ptr → FreeTemps → epred),
    ::wpPR
      [region: "bar" @ p'; "foo" @ p; [this := this]; return {?: "void*"}]
      {e: ($"foo" + $"bar")}
      Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr → ptr → ptr → (ptr → FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_prval_nowrap ti _Σ Σ σ tu p p' this Q%_function_scope
  NOTATION_wp_prval_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' p'' p''' this : ptr) 
    (Q : ptr → FreeTemps → epred),
    ::wpPR
      [region:
        "qux" @ p'''; "baz" @ p''; "bar" @ p'; "foo" @ p; 
        [this := this]; return {?: "void*"}]
      {e: ($"foo" + $"bar")}
      Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr → ptr → ptr → ptr → ptr → (ptr → FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_prval_wrap ti _Σ Σ σ tu p p' 
    p'' p''' this Q%_function_scope
  NOTATION_wp_operand_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' this : ptr) 
    (Q : val → FreeTemps → epred),
    ::wpOperand
      [region: "bar" @ p'; "foo" @ p; [this := this]; return {?: "void*"}]
      {e: ($"foo" + $"bar")}
      Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr → ptr → ptr → (val → FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_operand_nowrap ti _Σ Σ σ tu p p' this Q%_function_scope
  NOTATION_wp_operand_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' p'' p''' this : ptr) 
    (Q : val → FreeTemps → epred),
    ::wpOperand
      [region:
        "qux" @ p'''; "baz" @ p''; "bar" @ p'; "foo" @ p; 
        [this := this]; return {?: "void*"}]
      {e: ($"foo" + $"bar")}
      Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr → ptr → ptr → ptr → ptr → (val → FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_operand_wrap ti _Σ Σ σ tu p 
    p' p'' p''' this Q%_function_scope
  NOTATION_wp_xval_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' this : ptr) 
    (Q : ptr → FreeTemps → epred),
    ::wpX
      [region: "bar" @ p'; "foo" @ p; [this := this]; return {?: "void*"}]
      {e: ($"foo" + $"bar")}
      Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr → ptr → ptr → (ptr → FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_xval_nowrap ti _Σ Σ σ tu p p' this Q%_function_scope
  NOTATION_wp_xval_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' p'' p''' this : ptr) 
    (Q : ptr → FreeTemps → epred),
    ::wpX
      [region:
        "qux" @ p'''; "baz" @ p''; "bar" @ p'; "foo" @ p; 
        [this := this]; return {?: "void*"}]
      {e: ($"foo" + $"bar")}
      Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr → ptr → ptr → ptr → ptr → (ptr → FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_xval_wrap ti _Σ Σ σ tu p p' 
    p'' p''' this Q%_function_scope
  NOTATION_wp_glval_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' this : ptr) 
    (Q : ptr → FreeTemps → epred),
    ::wpGL
      [region: "bar" @ p'; "foo" @ p; [this := this]; return {?: "void*"}]
      {e: ($"foo" + $"bar")}
      Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr → ptr → ptr → (ptr → FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_glval_nowrap ti _Σ Σ σ tu p p' this Q%_function_scope
  NOTATION_wp_glval_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' p'' p''' this : ptr) 
    (Q : ptr → FreeTemps → epred),
    ::wpGL
      [region:
        "qux" @ p'''; "baz" @ p''; "bar" @ p'; "foo" @ p; 
        [this := this]; return {?: "void*"}]
      {e: ($"foo" + $"bar")}
      Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr → ptr → ptr → ptr → ptr → (ptr → FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_glval_wrap ti _Σ Σ σ tu p p' 
    p'' p''' this Q%_function_scope
  NOTATION_wp_discard_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p this : ptr) 
    (Q : FreeTemps → mpred),
    ::wpGLₓ
      [region: "foo" @ p; [this := this]; return {?: "void*"}]
      {e: ($"foo" + $"bar")}
      Q
       : ∀ (ti : biIndex) (_Σ : gFunctors),
           cpp_logic ti _Σ
           → genv → translation_unit → ptr → ptr → (FreeTemps → mpred) → mpred
  
  Arguments NOTATION_wp_discard_nowrap ti _Σ Σ σ tu p this Q%_function_scope
  NOTATION_wp_discard_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p this : ptr) 
    (Q : FreeTemps → mpred),
    ::wpGLₓ
      [region: "foo" @ p; [this := this]; return {?: "void*"}]
      {e: ($"foo" + $"bar")}
      Q
       : ∀ (ti : biIndex) (_Σ : gFunctors),
           cpp_logic ti _Σ
           → genv → translation_unit → ptr → ptr → (FreeTemps → mpred) → mpred
  
  Arguments NOTATION_wp_discard_nowrap ti _Σ Σ σ tu p this Q%_function_scope
  NOTATION_wp_func =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (F : Func) (ls : list ptr) 
    (Q : ptr → epred), ::wpFunc Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → translation_unit → Func → list ptr → (ptr → epred) → mpred
  
  Arguments NOTATION_wp_func ti _Σ Σ σ tu F ls%_list_scope Q%_function_scope
  NOTATION_wp_method =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (M : Method) 
    (ls : list ptr) (Q : ptr → epred), ::wpMethod Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → translation_unit → Method → list ptr → (ptr → epred) → mpred
  
  Arguments NOTATION_wp_method ti _Σ Σ σ tu M ls%_list_scope Q%_function_scope
  NOTATION_wp_ctor =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (C : Ctor) (ls : list ptr) 
    (Q : ptr → epred), ::wpCtor Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → translation_unit → Ctor → list ptr → (ptr → epred) → mpred
  
  Arguments NOTATION_wp_ctor ti _Σ Σ σ tu C ls%_list_scope Q%_function_scope
  NOTATION_wp_dtor =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (D : Dtor) (ls : list ptr) 
    (Q : ptr → epred), ::wpDtor Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → translation_unit → Dtor → list ptr → (ptr → epred) → mpred
  
  Arguments NOTATION_wp_dtor ti _Σ Σ σ tu D ls%_list_scope Q%_function_scope
  NOTATION_wp_args_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' this : ptr) 
    (tys_ar : evaluation_order.t) (es : list (wp.WPE.M ptr)) 
    (Q : list decltype * function_arity),
    ::wpArgs
      [region: "bar" @ p'; "foo" @ p; [this := this]; return {?: "void*"}]
      Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr
               → ptr
                 → ptr
                   → evaluation_order.t
                     → list (wp.WPE.M ptr)
                       → list decltype * function_arity
                         → list Expr
                           → (list ptr
                              → list ptr → FreeTemps → FreeTemps → mpred)
                             → mpred
  
  Arguments NOTATION_wp_args_nowrap ti _Σ Σ σ tu p p' 
    this tys_ar es%_list_scope Q es%_list_scope Q%_function_scope
  NOTATION_wp_args_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' p'' p''' this : ptr) 
    (tys_ar : evaluation_order.t) (es : list (wp.WPE.M ptr)) 
    (Q : list decltype * function_arity),
    ::wpArgs
      [region:
        "qux" @ p'''; "baz" @ p''; "bar" @ p'; "foo" @ p; 
        [this := this]; return {?: "void*"}]
      Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr
               → ptr
                 → ptr
                   → ptr
                     → ptr
                       → evaluation_order.t
                         → list (wp.WPE.M ptr)
                           → list decltype * function_arity
                             → list Expr
                               → (list ptr
                                  → list ptr → FreeTemps → FreeTemps → mpred)
                                 → mpred
  
  Arguments NOTATION_wp_args_wrap ti _Σ Σ σ tu p p' 
    p'' p''' this tys_ar es%_list_scope Q es%_list_scope 
    Q%_function_scope
  NOTATION_wp_initialize_nowrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p this : ptr) 
    (Q : FreeTemps → epred),
    ::wpInitialize
      [region: "foo" @ p; [this := this]; return {?: "void*"}]
      (p |-> type_ptrR {?: "void*"})
      {e: ($"foo" + $"bar")}
      Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv → translation_unit → ptr → ptr → (FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_initialize_nowrap ti _Σ Σ σ tu p this Q%_function_scope
  NOTATION_wp_initialize_wrap =
  λ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ) 
    (σ : genv) (tu : translation_unit) (p p' p'' p''' this : ptr) 
    (Q : FreeTemps → epred),
    ::wpInitialize
      [region:
        "qux" @ p'''; "baz" @ p''; "bar" @ p'; "foo" @ p; 
        [this := this]; return {?: "void*"}]
      (p |-> type_ptrR {?: "void*"})
      {e: ($"foo" + $"bar")}
      Q
       : ∀ (ti : biIndex) (_Σ : gFunctors) (Σ : cpp_logic ti _Σ),
           genv
           → translation_unit
             → ptr → ptr → ptr → ptr → ptr → (FreeTemps → epred) → mpred
  
  Arguments NOTATION_wp_initialize_wrap ti _Σ Σ σ tu 
    p p' p'' p''' this Q%_function_scope
