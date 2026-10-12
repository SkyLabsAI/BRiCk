  $ setup_project

Compiling patterns and actual specializations.
  $ make 2> /dev/null

Checking runtime/template separation and actual instantiated layout.
  $ dune build
