A builtin that clang marks as a library function (attribute F) prints as a
call to that function, with the `__builtin_` prefix stripped, as in clang's
CodeGen. Other builtins stay `Ebuiltin`.

Without a declaration of the library function, cpp2v declares it once, as
clang would implicitly, and `--check-types` accepts the calls. A function
that is not a builtin itself (`__memcpy_chk`) gets the type of its
`__builtin_` form. The declarations have no body: a `Builtin` body would make
BRiCk compare their parameter names with a header's (`ObjValue_le`).
  $ CRAM_CPP2VFLAGS=--no-sharing check_cpp2v nodecl.cpp
  cpp2v -v -check-types -o nodecl_17_cpp.v nodecl.cpp --no-sharing -- -std=c++17 2>&1 | sed 's/^ *[0-9]* | //'
  rocq c -w -notation-overridden -w -notation-incompatible-prefix nodecl_17_cpp.v
  $ grep -o 'Cfun2ptr (Eglobal (Nglobal (Nid "[a-z_]*"))\|Ebuiltin (Nglobal (Nid "[a-z_]*"))' nodecl_17_cpp.v
  Cfun2ptr (Eglobal (Nglobal (Nid "memcpy"))
  Cfun2ptr (Eglobal (Nglobal (Nid "memcpy"))
  Cfun2ptr (Eglobal (Nglobal (Nid "strlen"))
  Cfun2ptr (Eglobal (Nglobal (Nid "__memcpy_chk"))
  Ebuiltin (Nglobal (Nid "__builtin_object_size"))
  $ decl() {
  >   grep -A3 "(Dfunction (Nglobal (Nid \"$2\"))" $1 |
  >   sed -e 's/((localname.anon [0-9]*), /(/g' -e 's/("[a-z_0-9]*", /(/g'
  > }
  $ decl nodecl_17_cpp.v memcpy
      (Dfunction (Nglobal (Nid "memcpy"))
        (Build_Func (Tptr Tvoid)
          (((Tptr Tvoid)) :: ((Tptr (Qconst Tvoid))) :: (Tulong) :: nil) CC_C Ar_Definite exception_spec.NoThrow
          None))
  $ grep -c '(Dfunction (Nglobal (Nid "memcpy"))' nodecl_17_cpp.v
  1
  $ decl nodecl_17_cpp.v __memcpy_chk
      (Dfunction (Nglobal (Nid "__memcpy_chk"))
        (Build_Func (Tptr Tvoid)
          (((Tptr Tvoid)) :: ((Tptr (Qconst Tvoid))) :: (Tulong) :: (Tulong) :: nil) CC_C Ar_Definite exception_spec.NoThrow
          None))

The declaration of `memcpy` has the type that `<cstring>` gives it,
`noexcept` included (parameter names aside); `<cstring>`'s has a `Builtin`
body. In BRiCk, ours is below `<cstring>`'s (`ObjValue_le`, in test.v).
  $ cpp2v_command --no-sharing -o decl_cpp.v decl.cpp -- -std=c++17
  $ diff <(decl nodecl_17_cpp.v memcpy | head -3) <(decl decl_cpp.v memcpy | head -3) && echo same
  same
  $ decl decl_cpp.v memcpy | tail -1
          (Some (Builtin "memcpy"))))
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix decl_cpp.v
  $ rocq c -w -notation-overridden -w -notation-incompatible-prefix test.v

With a declaration (from <cstring>): exactly the ordinary call to it, and
no second declaration.
  $ callee() {
  >   awk -v f="\"$1\"" 'index($0, "(Dfunction (Nglobal (Nfunction function_qualifiers.N " f) {x=1}
  >                      x && /Cfun2ptr/ {print; getline; print; exit}' decl_cpp.v
  > }
  $ callee m
                      (Ecast Cfun2ptr (Eglobal (Nglobal (Nid "memcpy"))
                          (Tfunction type CC_C Ar_Definite (Tptr Tvoid) ((Tptr Tvoid) :: (Tptr (Qconst Tvoid)) :: Tulong :: nil))))
  $ test "$(callee m)" = "$(callee o)" && echo same
  same
  $ grep -c '(Dfunction (Nglobal (Nid "memcpy"))' decl_cpp.v
  1
