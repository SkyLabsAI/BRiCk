  $ . ../setup-project.sh

Compiling the Coq test file.
  $ dune build 2>&1 | sed -E -e 's!([ .]|^)/[^ :"]*!\1<path>!g'
  length
       : forall A : Type, list A -> nat
  source1
       : translation_unit.translation_unit
  source2
       : translation_unit.translation_unit
  @length
       : forall A : Type, list A -> nat







