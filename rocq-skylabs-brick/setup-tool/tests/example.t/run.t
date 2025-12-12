  $ . ../setup.sh
  $ find . | sort
  .
  ./Makefile
  ./br-project.toml
  ./dummy.opam
  ./dune-project
  ./include
  ./include/junk.hpp
  ./include/util.hpp
  ./src
  ./src/client
  ./src/client/br-config.toml
  ./src/client/client.cpp
  ./src/client/include
  ./src/client/include/client.hpp
  ./src/server
  ./src/server/attic
  ./src/server/attic/junk.cpp
  ./src/server/attic/todo.cpp
  ./src/server/br-config.toml
  ./src/server/include
  ./src/server/include/server.hpp
  ./src/server/server.cpp
  $ br gen --debug
  Changed directory to [$TESTCASE_ROOT].
  Initial directory was [.].
  File [include/util.hpp]:
   - coq_dirpath: my.project.include
   - clang_includes: ../include
  Creating directory [include/proof/util_hpp].
  File [src/client/client.cpp]:
   - coq_dirpath: my.project.src.client
   - clang_includes: ../../include, include
  Creating directory [src/client/proof/client_cpp].
  File [src/client/include/client.hpp]:
   - coq_dirpath: my.project.src.client.include
   - clang_includes: ../../../include, ../include
  Creating directory [src/client/include/proof/client_hpp].
  File [src/server/include/server.hpp]:
   - coq_dirpath: my.project.src.server.include
   - clang_includes: ../../../include, ../include
  Creating directory [src/server/include/proof/server_hpp].
  File [src/server/server.cpp]:
   - coq_dirpath: my.project.src.server
   - clang_includes: ../../include, include
  Creating directory [src/server/proof/server_cpp].
  $ find . | sort
  .
  ./Makefile
  ./br-project.toml
  ./dummy.opam
  ./dune-project
  ./include
  ./include/junk.hpp
  ./include/proof
  ./include/proof/util_hpp
  ./include/proof/util_hpp/dune
  ./include/util.hpp
  ./src
  ./src/client
  ./src/client/br-config.toml
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
  ./src/server/attic
  ./src/server/attic/junk.cpp
  ./src/server/attic/todo.cpp
  ./src/server/br-config.toml
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
    bluerock.lang
    Equations))
  (rule
   (targets code.v names.v)
   (deps
    (:input ../../client.cpp)
    (glob_files_rec ../../../../include/*.hpp)
    (glob_files_rec ../../include/*.hpp))
   (action
    (run cpp2v -v %{input} -o code.v -names names.v --
     -I../../../../include
     -I../../include)))
