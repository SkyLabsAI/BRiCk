  $ . ./setup.sh
  $ mkdir project && cd project
  $ touch br-project.toml
  $ br init
  Error: you are running the command from within a project.
  The project root is [$TESTCASE_ROOT/project].
  [1]
  $ mkdir subdir && cd subdir
  $ br init
  Error: you are running the command from within a project.
  The project root is [$TESTCASE_ROOT/project].
  [1]
