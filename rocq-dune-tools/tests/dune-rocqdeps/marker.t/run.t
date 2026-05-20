  $ test_root=$(mktemp -d "${TMPDIR:-/tmp}/dune-rocqdeps-marker.XXXXXX")
  $ tool="$(command -v dune-rocqdeps)"
  $ cd "$test_root"
  $ cat > dune-project <<'EOF'
  > (lang dune 3.21)
  > (name cram_dune_rocqdeps_marker)
  > (using rocq 0.11)
  > EOF
  $ mkdir -p workspace/a workspace/b workspace/c
  $ cat > workspace/b/dune <<'EOF'
  > (rocq.theory
  >  (name b))
  > EOF
  $ cat > workspace/c/dune <<'EOF'
  > (rocq.theory
  >  (name c))
  > EOF
  $ cat > workspace/a/dune <<'EOF'
  > (rocq.theory
  >  (name a)
  >  (theories
  >   b
  >   ; transitive dependencies example follows
  >   c
  >  ))
  > EOF
  $ cd workspace/a
  $ env -u DUNE_SOURCEROOT -u DUNE_ROOT "$tool"
  $ cat dune
  (rocq.theory
   (name a)
   (theories
    b
    ; transitive dependencies example follows
    c
   ))
  $ cat > dune <<'EOF'
  > (rocq.theory
  >  (name a)
  >  (theories
  >   b
  >   ; transitive dependencies
  >   c
  >  ))
  > EOF
  $ env -u DUNE_SOURCEROOT -u DUNE_ROOT "$tool"
  $ cat dune
  (rocq.theory
   (name a)
   (theories
    b
   ))
  $ cat > dune <<'EOF'
  > (rocq.theory
  >  (name a)
  >  (theories
  >   b
  >   ; transitive dependencies
  >   c
  >   ; transitive dependencies
  >  ))
  > EOF
  $ env -u DUNE_SOURCEROOT -u DUNE_ROOT "$tool" 2>&1 | sed -n '1p'
  error: Multiple transitive dependency markers in theories stanza
