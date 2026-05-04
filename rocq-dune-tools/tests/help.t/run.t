  $ dune-rocqproject --help=plain | sed -n '1,26p'
  NAME
         dune-rocqproject - generate _CoqProject content from rocq.theory
         stanzas
  
  SYNOPSIS
         dune-rocqproject [--coq-flags=FILE] [--prefix=PREFIX] [--root=DIR]
         [OPTION]…
  
  DESCRIPTION
         Generate _CoqProject content for Rocq projects that are organized in a
         dune workspaces.
  
         dune-rocqproject scans the selected workspace root, discovers
         rocq.theory stanzas, and prints the corresponding _CoqProject
         contents.
  
         The contents of the _CoqProject file are constructed by using:
         1/ built-in warning settings;
         2/ optional contents from --coq-flags;
         3/ -Q paths for the project and each of its dependencies to the workspace
            build directory; and
         4/ -Q paths for each project and its dependencies to the source directory.
            Build-directory paths come from dune describe workspace.
  
         Directories whose physical path ends in /elpi emit only the build-tree
         mapping.
