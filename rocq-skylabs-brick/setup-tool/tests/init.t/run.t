  $ . ../setup.sh
  $ find . | sort
  .
  ./Makefile
  ./dummy.opam
  ./dune-project
  ./include
  ./include/util.hpp
  ./src
  ./src/client
  ./src/client/client.cpp
  ./src/client/include
  ./src/client/include/client.hpp
  ./src/server
  ./src/server/include
  ./src/server/include/server.hpp
  ./src/server/server.cpp
  $ br init --coq-dirpath my.project --coq-package dummy -I include -I src/client/include -I src/server/include --flags=-Werror,-Wall,-Wextra
  $ cat br-project.toml
  # Project configuration file (at the root of the workspace).
  
  [coq]
  dirpath = "my.project"
  package = "dummy"
  theories = []
  
  [clang]
  includes = ["include", "src/client/include", "src/server/include"]
  flags = ["-Werror", "-Wall", "-Wextra"]
  
  [project]
  ignored = []
  $ br gen
  $ find . | sort
  .
  ./Makefile
  ./br-project.toml
  ./dummy.opam
  ./dune-project
  ./include
  ./include/proof
  ./include/proof/util_hpp
  ./include/proof/util_hpp/dune
  ./include/util.hpp
  ./src
  ./src/client
  ./src/client/client.cpp
  ./src/client/include
  ./src/client/include/client.hpp
  ./src/client/include/proof
  ./src/client/include/proof/client_hpp
  ./src/client/include/proof/client_hpp/dune
  ./src/client/proof
  ./src/client/proof/client_cpp
  ./src/client/proof/client_cpp/dune
  ./src/server
  ./src/server/include
  ./src/server/include/proof
  ./src/server/include/proof/server_hpp
  ./src/server/include/proof/server_hpp/dune
  ./src/server/include/server.hpp
  ./src/server/proof
  ./src/server/proof/server_cpp
  ./src/server/proof/server_cpp/dune
  ./src/server/server.cpp
  $ dune build
  $ find _build/default -name "*.vo" | sort
  _build/default/include/proof/util_hpp/code.vo
  _build/default/include/proof/util_hpp/names.vo
  _build/default/src/client/include/proof/client_hpp/code.vo
  _build/default/src/client/include/proof/client_hpp/names.vo
  _build/default/src/client/proof/client_cpp/code.vo
  _build/default/src/client/proof/client_cpp/names.vo
  _build/default/src/server/include/proof/server_hpp/code.vo
  _build/default/src/server/include/proof/server_hpp/names.vo
  _build/default/src/server/proof/server_cpp/code.vo
  _build/default/src/server/proof/server_cpp/names.vo
  $ cat src/client/proof/client_cpp/dune
  (include_subdirs qualified)
  (coq.theory
   (name my.project.src.client.client_cpp)
   (package dummy)
   (flags (:standard -w -notation-incompatible-prefix))
   (theories
    Stdlib
    stdpp
    iris
    elpi
    elpi_elpi
    Lens
    Ltac2
    bluerock.upoly
    bluerock.prelude
    bluerock.lang))
  (rule
   (targets code.v names.v)
   (deps
    (:input ../../client.cpp)
    (glob_files_rec ../../../../include/*.hpp)
    (glob_files_rec ../../../../src/client/include/*.hpp)
    (glob_files_rec ../../../../src/server/include/*.hpp))
   (action
    (run cpp2v -v %{input} -o code.v -names names.v --
     -I../../../../include
     -I../../../../src/client/include
     -I../../../../src/server/include
     -Werror -Wall -Wextra)))
