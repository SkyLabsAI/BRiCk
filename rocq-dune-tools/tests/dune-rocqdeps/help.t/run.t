  $ tool="$(command -v dune-rocqdeps)"
  $ "$tool" --help=plain | sed -n '1,36p'
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
  
         Canonical rewrites may differ textually from other accepted layouts.
         With --check, use the diff as guidance and trust the exit status.
  
  OPTIONS
         --ascii
             When used with --check, print diff output without ANSI escape
             codes.
  
         --check
             Do not edit dune files. Print a patdiff against the canonical
             rewrite that dune-rocqdeps would produce. The diff may include
             normalization-only changes and need not be the minimal patch that
             makes --check pass; the exit status reflects the dependency
             comparison.
  
         --no-normalize
             Only append newly discovered dependencies. Existing dependency
             order is preserved, and files are unchanged when no new
             dependencies are needed.
