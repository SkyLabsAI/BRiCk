  $ tool="$(command -v dune-rocqdeps)"
  $ "$tool" --help=plain | sed -n '1,35p'
  NAME
         dune-rocqdeps - synchronize recursive rocq dependency stanzas in dune
         files
  
  SYNOPSIS
         dune-rocqdeps [--ascii] [--check] [--no-normalize] [OPTION]…
  
  DESCRIPTION
         dune-rocqdeps scans the current dune workspace, rewrites rocq.theory
         (theories ...) fields in the current directory subtree, and expands
         them with recursive transitive dependencies.
  
         Rewritten stanzas list direct dependencies first and then a ;
         transitive dependencies section. Once a file uses that style, only the
         pre-marker entries are treated as direct roots when the closure is
         recomputed.
  
  OPTIONS
         --ascii
             When used with --check, print diff output without ANSI escape
             codes.
  
         --check
             Do not edit dune files. Print patdiff output to stdout and exit
             unsuccessfully if the selected rocq.theory stanzas need changes.
  
         --no-normalize
             Only append newly discovered dependencies. Existing dependency
             order is preserved, and files are unchanged when no new
             dependencies are needed.
  
  COMMON OPTIONS
         --help[=FMT] (default=auto)
             Show this help in format FMT. The value FMT must be one of auto,
             pager, groff or plain. With auto, the format is pager or plain
