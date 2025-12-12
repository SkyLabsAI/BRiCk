  $ . ../setup-project.sh

Compiling the Coq test file.
  $ dune build
  module =
  {|
    symbols :=
      {|
        TM.this := NM.Raw.Leaf ObjValue;
        TM.is_bst :=
          internal.NameMap.check_canon_ok (internal.NameMap.Raw.Leaf ObjValue)
            I
      |};
    types :=
      {|
        TM.this :=
          NM.Raw.Node
            (NM.Raw.Node (NM.Raw.Leaf GlobDecl) "align_val_t"%cpp_name Gtype
               (NM.Raw.Leaf GlobDecl) 1%Z)
            "xx"%cpp_name (Gtypedef "align_val_t") (NM.Raw.Leaf GlobDecl) 2%Z;
        TM.is_bst :=
          internal.NameMap.check_canon_ok
            (internal.NameMap.Raw.Node
               (internal.NameMap.Raw.Node (internal.NameMap.Raw.Leaf GlobDecl)
                  "align_val_t"%cpp_name Gtype
                  (internal.NameMap.Raw.Leaf GlobDecl) 1%Z)
               "xx"%cpp_name (Gtypedef "align_val_t")
               (internal.NameMap.Raw.Leaf GlobDecl) 2%Z)
            I
      |};
    namespace_aliases :=
      ({| listset_car := [] |},
       {|
         TM.this := NM.Raw.Leaf (listset name);
         TM.is_bst :=
           internal.NameMap.check_canon_ok
             (internal.NameMap.Raw.Leaf (listset name)) I
       |});
    initializer := [];
    byte_order := Little
  |}
       : translation_unit
