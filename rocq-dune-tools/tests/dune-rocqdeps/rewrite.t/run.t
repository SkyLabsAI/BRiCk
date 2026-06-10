  $ test_root=$(mktemp -d "${TMPDIR:-/tmp}/dune-rocqdeps-rewrite.XXXXXX")
  $ tool="$(command -v dune-rocqdeps)"
  $ cd "$test_root"
  $ cat > dune-project <<'EOF'
  > (lang dune 3.22)
  > (name cram_dune_rocqdeps_rewrite)
  > (using rocq 0.12)
  > EOF
  $ mkdir -p workspace/a workspace/b workspace/c workspace/sibling
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
  $ cat > workspace/sibling/dune <<'EOF'
  > (rocq.theory
  >  (name sibling)
  >  (theories b))
  > EOF
  $ cd workspace/a
  $ env -u DUNE_SOURCEROOT -u DUNE_ROOT "$tool"
  $ cat dune
  (rocq.theory
   (name a)
   (theories c b))
  $ cat ../b/dune
  (rocq.theory
   (name b)
   (theories c))
  $ cat ../sibling/dune
  (rocq.theory
   (name sibling)
   (theories b))
  $ cat > dune <<'EOF'
  > (rocq.theory
  >  (name a)
  >  (theories
  >   b
  >   ; transitive dependencies
  >   c
  >  ))
  > EOF
  $ cat > ../b/dune <<'EOF'
  > (rocq.theory
  >  (name b))
  > EOF
  $ env -u DUNE_SOURCEROOT -u DUNE_ROOT "$tool"
  $ cat dune
  (rocq.theory
   (name a)
   (theories
    b
   ))
