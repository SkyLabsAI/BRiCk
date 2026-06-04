  $ test_root=$(mktemp -d "${TMPDIR:-/tmp}/dune-rocqdeps-ansi.XXXXXX")
  $ tool="$(command -v dune-rocqdeps)"
  $ cd "$test_root"
  $ cat > dune-project <<'EOF'
  > (lang dune 3.21)
  > (name cram_dune_rocqdeps_ansi)
  > (using rocq 0.11)
  > EOF
  $ mkdir -p a b c
  $ cat > a/dune <<'EOF'
  > (rocq.theory
  >  (name a)
  >  (theories b))
  > EOF
  $ cat > b/dune <<'EOF'
  > (rocq.theory
  >  (name b)
  >  (theories c))
  > EOF
  $ cat > c/dune <<'EOF'
  > (rocq.theory
  >  (name c))
  > EOF
  $ cd a

The default check diff uses ANSI escape codes. Cram strips raw ANSI escapes
from command output, so use sed to make them printable before cram sees them.

  $ env -u DUNE_SOURCEROOT -u DUNE_ROOT "$tool" --check | sed -n l
  \033[0;31m------ \033[0m\033[0;1mold/dune\033[0m$
  \033[0;32m++++++ \033[0m\033[0;1mnew/dune\033[0m$
  \033[0;100;30m@|\033[0m\033[0;1m-1,3 +1,7\033[0m ==========\
  ==================================================$
  \033[0;100;30m |\033[0m(rocq.theory$
  \033[0;100;30m |\033[0m (name a)$
  \033[0;43;30m!|\033[0m (theories$
  \033[0;43;30m!|\033[0m  b$
  \033[0;43;30m!|\033[0m\033[0;32m  ; transitive dependencies\
  \033[0m$
  \033[0;43;30m!|\033[0m\033[0;32m  c\033[0m$
  \033[0;43;30m!|\033[0m ))$
