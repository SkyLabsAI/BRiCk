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
