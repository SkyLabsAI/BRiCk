  $ test_root=$(mktemp -d "${TMPDIR:-/tmp}/dune-rocqdeps-check.XXXXXX")
  $ tool="$(command -v dune-rocqdeps)"
  $ cd "$test_root"
  $ cat > dune-project <<'EOF'
  > (lang dune 3.21)
  > (name cram_dune_rocqdeps_check)
  > (using rocq 0.11)
  > EOF
  $ mkdir -p workspace/a workspace/b workspace/c
  $ cat > workspace/a/dune <<'EOF'
  > (rocq.theory
  >  (name a)
  >  (theories b))
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

Check mode reports stale files without rewriting them:

  $ env -u DUNE_SOURCEROOT -u DUNE_ROOT "$tool" --check --ascii
  ------ old/dune
  ++++++ new/dune
  @|-1,3 +1,7 ============================================================
   |(rocq.theory
   | (name a)
  -| (theories b))
  +| (theories
  +|  b
  +|  ; transitive dependencies
  +|  c
  +| ))
  [1]
  $ cat dune
  (rocq.theory
   (name a)
   (theories b))

After a normal rewrite, check mode succeeds:

  $ env -u DUNE_SOURCEROOT -u DUNE_ROOT "$tool"
  $ cat dune
  (rocq.theory
   (name a)
   (theories
    b
    ; transitive dependencies
    c
   ))

  $ env -u DUNE_SOURCEROOT -u DUNE_ROOT "$tool" --check --ascii

Check mode accepts files that already contain the full dependency closure,
even when they have not been normalized by dune-rocqdeps:

  $ cat > dune <<'EOF'
  > (rocq.theory
  >  (name a)
  >  (theories c  b))
  > EOF
  $ env -u DUNE_SOURCEROOT -u DUNE_ROOT "$tool" --check --ascii
  $ cat dune
  (rocq.theory
   (name a)
   (theories c  b))

Check mode rejects stale dependencies in the transitive dependency section:

  $ cat > ../b/dune <<'EOF'
  > (rocq.theory
  >  (name b))
  > EOF
  $ cat > dune <<'EOF'
  > (rocq.theory
  >  (name a)
  >  (theories
  >   b
  >   ; transitive dependencies
  >   c
  >  ))
  > EOF
  $ env -u DUNE_SOURCEROOT -u DUNE_ROOT "$tool" --check --ascii
  ------ old/dune
  ++++++ new/dune
  @|-1,7 +1,5 ============================================================
   |(rocq.theory
   | (name a)
   | (theories
   |  b
  -|  ; transitive dependencies
  -|  c
   | ))
  [1]
  $ cat dune
  (rocq.theory
   (name a)
   (theories
    b
    ; transitive dependencies
    c
   ))

Without check mode, the tool removes the stale transitive dependency:

  $ env -u DUNE_SOURCEROOT -u DUNE_ROOT "$tool"
  $ cat dune
  (rocq.theory
   (name a)
   (theories
    b
   ))
