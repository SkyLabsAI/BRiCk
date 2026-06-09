  $ test_root=$(mktemp -d "${TMPDIR:-/tmp}/dune-rocqdeps-no-normalize.XXXXXX")
  $ tool="$(command -v dune-rocqdeps)"
  $ cd "$test_root"
  $ cat > dune-project <<'EOF'
  > (lang dune 3.22)
  > (name cram_dune_rocqdeps_no_normalize)
  > (using rocq 0.12)
  > EOF
  $ mkdir -p workspace/a workspace/b workspace/c
  $ cat > workspace/a/dune <<'EOF'
  > (rocq.theory
  >  (name a)
  >  (theories c b))
  > EOF
  $ cat > workspace/b/dune <<'EOF'
  > (rocq.theory
  >  (name b)
  >  (theories c))
  > EOF
  $ cat > workspace/c/dune <<'EOF'
  > (rocq.theory
  >  (name c))
  > EOF
  $ cd workspace/a
  $ env -u DUNE_SOURCEROOT -u DUNE_ROOT "$tool" --no-normalize
  $ cat dune
  (rocq.theory
   (name a)
   (theories c b))
  $ cat > dune <<'EOF'
  > (rocq.theory
  >  (name a)
  >  (theories b))
  > EOF
  $ env -u DUNE_SOURCEROOT -u DUNE_ROOT "$tool" --no-normalize
  $ cat dune
  (rocq.theory
   (name a)
   (theories
    b
    ; transitive dependencies
    c
   ))
