  $ . ../setup-project.sh
  $ dune build test.vo
  Sseq_nil = {s: // end block}
       : Stmt
  Sseq_singleton = {s: return;
                       // end block}
       : Stmt
  Sseq_cons = {s: return;
                  {?: s};
                  return nullptr;
                  // end block}
       : Stmt
  
  Sseq_cons uses section variable s.
  Sdecl_nil = {s: // end decl block}
       : Stmt
  Sdecl_singleton_no_init = {s: {?: ty} $"foo";}
       : Stmt
  
  Sdecl_singleton_no_init uses section variable ty.
  Sdecl_singleton_init = {s: {?: ty} $"foo" = nullptr;}
       : Stmt
  
  Sdecl_singleton_init uses section variable ty.
  Sdecl_cons = {s: {?: ty} $"foo";
                   {?: ty} $"bar" = nullptr;}
       : Stmt
  
  Sdecl_cons uses section variable ty.
  Sif_no_decl = {s: if ($"is_true") {
                      return;
                    } else {
                      break;
                    }}
       : Stmt
  
  Sif_no_decl uses section variable ty.
  Sif_decl_no_init =
  {s: if ({?: ty} $"foo"; $"foo") {
        return;
      } else {
        break;
      }}
       : Stmt
  
  Sif_decl_no_init uses section variable ty.
  Sif_decl_init =
  {s: if ({?: ty} $"foo" = #314; $"foo") {
        return;
      } else {
        break;
      }}
       : Stmt
  
  Sif_decl_init uses section variable ty.
  Swhile_no_decl = {s: while ($"is_true") {
                         continue;
                       }}
       : Stmt
  
  Swhile_no_decl uses section variable ty.
  Swhile_decl_no_init =
  {s: while ({?: ty} $"foo"; $"foo") {
        continue;
      }}
       : Stmt
  
  Swhile_decl_no_init uses section variable ty.
  Swhile_decl_init =
  {s: while ({?: ty} $"foo" = #314; $"foo") {
        continue;
      }}
       : Stmt
  
  Swhile_decl_init uses section variable ty.
  Swhile_decl_init_multiline =
  {s: while ({?: ty} $"foo" = #314; $"foo") {
        continue;
        break;
        {?: s};
        return nullptr;
        // end block
      }}
       : Stmt
  
  Swhile_decl_init_multiline uses section variables ty s.
  Sfor_no_init_no_cond_no_incr_empty =
  {s: for (;;) {
        // end block
      }}
       : Stmt
  Sfor_no_init_no_cond_no_incr_singleton =
  {s: for (;;) {
        return;
        // end block
      }}
       : Stmt
  Sfor_no_init_no_cond_no_incr_multiline =
  {s: for (;;) {
        continue;
        break;
        {?: s};
        return nullptr;
        // end block
      }}
       : Stmt
  
  Sfor_no_init_no_cond_no_incr_multiline uses section variable s.
  Sfor_no_init_no_cond_incr_empty =
  {s: for (;; ++$"bar") {
        // end block
      }}
       : Stmt
  
  Sfor_no_init_no_cond_incr_empty uses section variable ty.
  Sfor_no_init_no_cond_incr_singleton =
  {s: for (;; ++$"bar") {
        return;
        // end block
      }}
       : Stmt
  
  Sfor_no_init_no_cond_incr_singleton uses section variable ty.
  Sfor_no_init_no_cond_incr_multiline =
  {s: for (;; ++$"bar") {
        continue;
        break;
        {?: s};
        return nullptr;
        // end block
      }}
       : Stmt
  
  Sfor_no_init_no_cond_incr_multiline uses section variables ty s.
  Sfor_no_init_cond_no_incr_empty =
  {s: for (; $"foo";) {
        // end block
      }}
       : Stmt
  
  Sfor_no_init_cond_no_incr_empty uses section variable ty.
  Sfor_no_init_cond_no_incr_singleton =
  {s: for (; $"foo";) {
        return;
        // end block
      }}
       : Stmt
  
  Sfor_no_init_cond_no_incr_singleton uses section variable ty.
  Sfor_no_init_cond_no_incr_multiline =
  {s: for (; $"foo";) {
        continue;
        break;
        {?: s};
        return nullptr;
        // end block
      }}
       : Stmt
  
  Sfor_no_init_cond_no_incr_multiline uses section variables ty s.
  Sfor_init_no_cond_no_incr_empty =
  {s: for ({?: ty} $"foo";
           {?: ty} $"bar" = #314;;) {
        // end block
      }}
       : Stmt
  
  Sfor_init_no_cond_no_incr_empty uses section variable ty.
  Sfor_init_no_cond_no_incr_singleton =
  {s: for ({?: ty} $"foo";
           {?: ty} $"bar" = #314;;) {
        return;
        // end block
      }}
       : Stmt
  
  Sfor_init_no_cond_no_incr_singleton uses section variable ty.
  Sfor_init_no_cond_no_incr_multiline =
  {s: for ({?: ty} $"foo";
           {?: ty} $"bar" = #314;;) {
        continue;
        break;
        {?: s};
        return nullptr;
        // end block
      }}
       : Stmt
  
  Sfor_init_no_cond_no_incr_multiline uses section variables ty s.
  Sfor_init_cond_no_incr_empty =
  {s: for ({?: ty} $"foo";
           {?: ty} $"bar" = #314; $"foo";) {
        // end block
      }}
       : Stmt
  
  Sfor_init_cond_no_incr_empty uses section variable ty.
  Sfor_init_cond_no_incr_singleton =
  {s: for ({?: ty} $"foo";
           {?: ty} $"bar" = #314; $"foo";) {
        return;
        // end block
      }}
       : Stmt
  
  Sfor_init_cond_no_incr_singleton uses section variable ty.
  Sfor_init_cond_no_incr_multiline =
  {s: for ({?: ty} $"foo";
           {?: ty} $"bar" = #314; $"foo";) {
        continue;
        break;
        {?: s};
        return nullptr;
        // end block
      }}
       : Stmt
  
  Sfor_init_cond_no_incr_multiline uses section variables ty s.
  Sfor_init_no_cond_incr_empty =
  {s: for ({?: ty} $"foo";
           {?: ty} $"bar" = #314;; ++$"bar") {
        // end block
      }}
       : Stmt
  
  Sfor_init_no_cond_incr_empty uses section variable ty.
  Sfor_init_no_cond_incr_singleton =
  {s: for ({?: ty} $"foo";
           {?: ty} $"bar" = #314;; ++$"bar") {
        return;
        // end block
      }}
       : Stmt
  
  Sfor_init_no_cond_incr_singleton uses section variable ty.
  Sfor_init_no_cond_incr_multiline =
  {s: for ({?: ty} $"foo";
           {?: ty} $"bar" = #314;; ++$"bar") {
        continue;
        break;
        {?: s};
        return nullptr;
        // end block
      }}
       : Stmt
  
  Sfor_init_no_cond_incr_multiline uses section variables ty s.
  Sfor_no_init_cond_incr_empty =
  {s: for (; $"foo"; ++$"bar") {
        // end block
      }}
       : Stmt
  
  Sfor_no_init_cond_incr_empty uses section variable ty.
  Sfor_no_init_cond_incr_singleton =
  {s: for (; $"foo"; ++$"bar") {
        return;
        // end block
      }}
       : Stmt
  
  Sfor_no_init_cond_incr_singleton uses section variable ty.
  Sfor_no_init_cond_incr_multiline =
  {s: for (; $"foo"; ++$"bar") {
        continue;
        break;
        {?: s};
        return nullptr;
        // end block
      }}
       : Stmt
  
  Sfor_no_init_cond_incr_multiline uses section variables ty s.
  Sfor_init_cond_incr_empty =
  {s: for ({?: ty} $"foo";
           {?: ty} $"bar" = #314; $"foo"; ++$"bar") {
        // end block
      }}
       : Stmt
  
  Sfor_init_cond_incr_empty uses section variable ty.
  Sfor_init_cond_incr_singleton =
  {s: for ({?: ty} $"foo";
           {?: ty} $"bar" = #314; $"foo"; ++$"bar") {
        return;
        // end block
      }}
       : Stmt
  
  Sfor_init_cond_incr_singleton uses section variable ty.
  Sfor_init_cond_incr_multiline =
  {s: for ({?: ty} $"foo";
           {?: ty} $"bar" = #314; $"foo"; ++$"bar") {
        continue;
        break;
        {?: s};
        return nullptr;
        // end block
      }}
       : Stmt
  
  Sfor_init_cond_incr_multiline uses section variables ty s.
  Sdo_empty = {s: do {
                    // end block
                  } while(#false);}
       : Stmt
  Sdo_singleton = {s: do {
                        continue;
                        // end block
                      } while(#true);}
       : Stmt
  Sdo_multiline =
  {s: do {
        continue;
        break;
        {?: s};
        return #217;
        // end block
      } while(#true);}
       : Stmt
  
  Sdo_multiline uses section variables ty s.
  {s: break;}
       : Stmt' ?obj_name ?type ?Expr
  where
  ?obj_name : [ty : type  e : Expr  s : Stmt |- Set]
  ?type : [ty : type  e : Expr  s : Stmt |- Set]
  ?Expr : [ty : type  e : Expr  s : Stmt |- Set]
  {s: continue;}
       : Stmt' ?obj_name ?type ?Expr
  where
  ?obj_name : [ty : type  e : Expr  s : Stmt |- Set]
  ?type : [ty : type  e : Expr  s : Stmt |- Set]
  ?Expr : [ty : type  e : Expr  s : Stmt |- Set]
  Sreturn_None = {s: return;}
       : Stmt
  Sreturn_Some = {s: return #314;}
       : Stmt
  
  Sreturn_Some uses section variable ty.
  Sexpr_simple = {s: nullptr;}
       : Stmt
  Sexpr_complex = {s: #true ? $"foo" : $"bar";}
       : Stmt
  
  Sexpr_complex uses section variable ty.
  Sattr_nil = {s: continue;}
       : Stmt
  Sattr_cons = {s: [["foo", "bar", "baz"]] break;}
       : Stmt
  {s: <LABEL: "FOO_BAR"> return;}
       : Stmt' ?obj_name ?type ?Expr
  where
  ?obj_name : [ty : type  e : Expr  s : Stmt |- Set]
  ?type : [ty : type  e : Expr  s : Stmt |- Set]
  ?Expr : [ty : type  e : Expr  s : Stmt |- Set]
  {s: goto "FOO_BAR";}
       : Stmt' ?obj_name ?type ?Expr
  where
  ?obj_name : [ty : type  e : Expr  s : Stmt |- Set]
  ?type : [ty : type  e : Expr  s : Stmt |- Set]
  ?Expr : [ty : type  e : Expr  s : Stmt |- Set]
  {s: <LABEL: "FOO_BAR"> continue;
      goto "FOO_BAR";
      // end block}
       : Stmt' ?obj_name ?type ?Expr
  where
  ?obj_name : [ty : type  e : Expr  s : Stmt |- Set]
  ?type : [ty : type  e : Expr  s : Stmt |- Set]
  ?Expr : [ty : type  e : Expr  s : Stmt |- Set]
  {e: {UNSUPPORTED: "This was an unsupported operation"}}
       : Expr
