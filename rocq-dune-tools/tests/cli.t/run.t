  $ dune-rocqproject --help=plain | sed -n '1,28p'
  NAME
         dune-rocqproject - generate _CoqProject content from rocq.theory
         stanzas
  
  SYNOPSIS
         dune-rocqproject [COMMAND] …
  
  DESCRIPTION
         Generate _CoqProject content for Rocq projects that are organized in a
         dune workspaces.
  
         When invoked without a subcommand, dune-rocqproject generates a
         _CoqProject file for the rocq.theories in the dune workspace.
  
         The contents of the _CoqProject file are constructed by using:
         1/ built-in warning settings;
         2/ optional contents from --coq-flags;
         3/ -Q paths for the project and each of its dependencies to the workspace
            build directory; and
         4/ -Q paths for each project and its dependencies to the source directory.
            Paths to the _build directory will target _default.
  
         Directories whose physical path ends in /elpi emit only the build-tree
         mapping. This preserves the behavior of the legacy helper scripts and
         avoids duplicate mappings for Elpi sources.
  
         Use the gather-coq-paths subcommand when only the mapping lines are
         needed.

  $ dune-rocqproject gather-coq-paths --help=plain | sed -n '1,18p'
  NAME
         dune-rocqproject-gather-coq-paths - print only the -Q mappings for
         selected dune files
  
  SYNOPSIS
         dune-rocqproject gather-coq-paths [--prefix=PREFIX] [OPTION]…
         DUNE_FILE…
  
  DESCRIPTION
         Parse the given dune files and print only the corresponding -Q mapping
         lines. This is the OCaml replacement for the old gather-coq-paths.py
         helper.
  
         If a dune file has no rocq.theory stanza or no theory name, it
         contributes no output.
  
  ARGUMENTS
         DUNE_FILE (required)

  $ mkdir -p workspace/pkg workspace/pkg/elpi workspace/.git/ignored workspace/_build/skipped
  $ cat > workspace/pkg/dune <<'EOF'
  > (rocq.theory
  >  (name smoke.pkg))
  > EOF
  $ cat > workspace/pkg/elpi/dune <<'EOF'
  > (rocq.theory
  >  (name smoke.elpi))
  > EOF
  $ cat > workspace/.git/ignored/dune <<'EOF'
  > (rocq.theory
  >  (name ignored.git))
  > EOF
  $ cat > workspace/_build/skipped/dune <<'EOF'
  > (rocq.theory
  >  (name ignored.build))
  > EOF
  $ cat > workspace/coq.flags <<'EOF'
  > -arg -w -arg -notation-overridden
  > EOF

  $ dune-rocqproject gather-coq-paths workspace/pkg/dune
  -Q _build/default/workspace/pkg/ smoke.pkg
  -Q workspace/pkg/ smoke.pkg

  $ dune-rocqproject gather-coq-paths workspace/pkg/elpi/dune
  -Q _build/default/workspace/pkg/elpi/ smoke.elpi

  $ dune-rocqproject --root workspace
  # AUTO-GENERATED CONTENT, EDIT `dune-rocqproject` INSTEAD
  
  # Avoid warnings about entries in this _CoqProject
  -arg -w -arg -cannot-open-path
  -arg -w -arg -notation-overridden
  
  # Plugin directory.
  -I _build/install/default/lib
  
  # Specified logical paths for directories (for .v and .vo files).
  -Q _build/default/pkg/ smoke.pkg
  -Q pkg/ smoke.pkg
  -Q _build/default/pkg/elpi/ smoke.elpi

  $ dune-rocqproject --root workspace --prefix vendor
  # AUTO-GENERATED CONTENT, EDIT `dune-rocqproject` INSTEAD
  
  # Avoid warnings about entries in this _CoqProject
  -arg -w -arg -cannot-open-path
  -arg -w -arg -notation-overridden
  
  # Plugin directory.
  -I _build/install/default/lib
  
  # Specified logical paths for directories (for .v and .vo files).
  -Q _build/default/vendor/pkg/ smoke.pkg
  -Q vendor/pkg/ smoke.pkg
  -Q _build/default/vendor/pkg/elpi/ smoke.elpi
