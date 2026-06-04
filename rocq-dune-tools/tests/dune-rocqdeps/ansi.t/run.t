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

The default check diff uses ANSI escape codes.

  $ env -u DUNE_SOURCEROOT -u DUNE_ROOT "$tool" --check | sed -n '1l'
  \033[0;31m------ \033[0m\033[0;1mold/dune\033[0m$
