  $ . ../setup-project.sh

Compiling the Coq test file.
  $ dune build 2>&1 | sed -E -e 's!([ .]|^)/[^ :"]*!\1<path>!g'
  source1
       : translation_unit
  source2
       : translation_unit







