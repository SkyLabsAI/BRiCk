  $ test_root=$(mktemp -d "${TMPDIR:-/tmp}/dune-rocqdeps-errors.XXXXXX")
  $ tool="$(command -v dune-rocqdeps)"
  $ cd "$test_root"
  $ cat > dune-project <<'EOF'
  > (lang dune 3.22)
  > (name cram_dune_rocqdeps_errors)
  > (using rocq 0.12)
  > EOF
  $ mkdir -p unresolved ambiguous-left ambiguous-right cycle-a cycle-b

Unresolved dependencies are reported when followed:

  $ cat > unresolved/dune <<'EOF'
  > (rocq.theory
  >  (name unresolved)
  >  (theories missing))
  > EOF
  $ cd unresolved
  $ env -u DUNE_SOURCEROOT -u DUNE_ROOT "$tool" 2>&1 | sed -n '1p'
  error: Unresolved theory dependency "missing"
  $ cd ..

Ambiguous theory names only fail when used:

  $ cat > ambiguous-left/dune <<'EOF'
  > (rocq.theory
  >  (name shared))
  > EOF
  $ cat > ambiguous-right/dune <<'EOF'
  > (rocq.theory
  >  (name shared))
  > EOF
  $ cat > unresolved/dune <<'EOF'
  > (rocq.theory
  >  (name unresolved)
  >  (theories shared))
  > EOF
  $ cd unresolved
  $ env -u DUNE_SOURCEROOT -u DUNE_ROOT "$tool" 2>&1 | sed -n '1p'
  error: Ambiguous theory dependency "shared" defined in:
  $ cd ..

Cycles are reported with the dependency path:

  $ rm unresolved/dune ambiguous-left/dune ambiguous-right/dune

  $ cat > cycle-a/dune <<'EOF'
  > (rocq.theory
  >  (name cycle.a)
  >  (theories cycle.b))
  > EOF
  $ cat > cycle-b/dune <<'EOF'
  > (rocq.theory
  >  (name cycle.b)
  >  (theories cycle.a))
  > EOF
  $ cd cycle-a
  $ env -u DUNE_SOURCEROOT -u DUNE_ROOT "$tool" 2>&1 | sed -n '1p'
  error: Dependency cycle detected: cycle.a -> cycle.b -> cycle.a
