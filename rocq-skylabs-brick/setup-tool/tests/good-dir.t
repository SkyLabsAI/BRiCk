  $ . ./setup.sh
  $ mkdir "good-dir"
  $ cd "good-dir"
  $ br init
  $ cat br-project.toml
  # Project configuration file (at the root of the workspace).
  
  [coq]
  dirpath = "br.project.good_dir"
  package = "good-dir"
  theories = []
  
  [clang]
  includes = []
  flags = []
  
  [project]
  ignored = []
