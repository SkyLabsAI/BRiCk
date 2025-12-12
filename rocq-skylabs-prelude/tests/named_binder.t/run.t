  $ . ../setup-project.sh
  $ dune build test.vo
  - : Init.constr = constr:(fun test : bool => @eq bool test test)
  - : Init.constr =
  constr:(fun test : bool =>
          @eq (prod bool bool) (@pair bool bool test true)
            (@pair bool bool test false))
  - : Init.constr =
  constr:(fun test : bool =>
          @eq (prod (NamedBinder bool "x") bool)
            (@pair (NamedBinder bool "x") bool test true)
            (@pair (NamedBinder bool "test") bool test false))
