  $ test_root=$(mktemp -d "${TMPDIR:-/tmp}/dune-rocqdeps-corelib.XXXXXX")
  $ tool="$(command -v dune-rocqdeps)"
  $ cd "$test_root"
  $ cat > dune-project <<'EOF'
  > (lang dune 3.22)
  > (name cram_dune_rocqdeps_corelib)
  > (using rocq 0.12)
  > EOF
  $ mkdir -p workspace/a workspace/ltac2
  $ cat > workspace/ltac2/dune <<'EOF'
  > (rocq.theory
  >  (name Ltac2)
  >  (theories Corelib))
  > EOF
  $ cat > workspace/a/dune <<'EOF'
  > (rocq.theory
  >  (name a)
  >  (theories Ltac2))
  > EOF
  $ cd workspace/a

Corelib is implicit: it is neither unresolved nor added transitively.

  $ env -u DUNE_SOURCEROOT -u DUNE_ROOT "$tool" --check --ascii
  $ cat dune
  (rocq.theory
   (name a)
   (theories Ltac2))

Corelib is removed when it appears as an explicit direct dependency.

  $ cat > dune <<'EOF'
  > (rocq.theory
  >  (name a)
  >  (theories Corelib Ltac2))
  > EOF
  $ env -u DUNE_SOURCEROOT -u DUNE_ROOT "$tool" --check --ascii
  ------ old/dune
  ++++++ new/dune
  @|-1,3 +1,5 ============================================================
   |(rocq.theory
   | (name a)
  -| (theories Corelib Ltac2))
  +| (theories
  +|  Ltac2
  +| ))
  [1]
  $ env -u DUNE_SOURCEROOT -u DUNE_ROOT "$tool"
  $ cat dune
  (rocq.theory
   (name a)
   (theories
    Ltac2
   ))

Stale Corelib entries are removed from transitive dependency sections.

  $ cat > dune <<'EOF'
  > (rocq.theory
  >  (name a)
  >  (theories
  >   Ltac2
  >   ; transitive dependencies
  >   Corelib
  >  ))
  > EOF
  $ env -u DUNE_SOURCEROOT -u DUNE_ROOT "$tool" --check --ascii
  ------ old/dune
  ++++++ new/dune
  @|-1,7 +1,5 ============================================================
   |(rocq.theory
   | (name a)
   | (theories
   |  Ltac2
  -|  ; transitive dependencies
  -|  Corelib
   | ))
  [1]
  $ env -u DUNE_SOURCEROOT -u DUNE_ROOT "$tool"
  $ cat dune
  (rocq.theory
   (name a)
   (theories
    Ltac2
   ))
