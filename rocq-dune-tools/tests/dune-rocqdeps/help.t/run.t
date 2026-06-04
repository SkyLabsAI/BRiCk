  $ tool="$(command -v dune-rocqdeps)"
  $ "$tool" --help=plain | sed -n '1,41p'
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
  
         The canonical rewrite may differ textually from other accepted
         layouts. When using --check, treat the printed diff as the canonical
         output rather than as a minimal required patch, and trust the exit
         status.
  
  OPTIONS
         --ascii
             When used with --check, print diff output without ANSI escape
             codes.
  
         --check
             Do not edit dune files. Print a patdiff against the canonical
             rewrite that dune-rocqdeps would produce. The printed diff is not
             necessarily a minimal patch required to make the check pass: it
             may include normalization-only changes such as ordering, grouping,
             comments, or line layout. The exit status is based on whether the
             selected rocq.theory dependency closures are stale under
             dune-rocqdeps' dependency comparison, not on whether file text
             exactly matches the printed rewrite.
  
         --no-normalize
             Only append newly discovered dependencies. Existing dependency
             order is preserved, and files are unchanged when no new
             dependencies are needed.
