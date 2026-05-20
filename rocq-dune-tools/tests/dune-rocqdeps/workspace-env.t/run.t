  $ test_root=$(mktemp -d "${TMPDIR:-/tmp}/dune-rocqdeps-workspace-env.XXXXXX")
  $ tool="$(command -v dune-rocqdeps)"
  $ cd "$test_root"
  $ mkdir -p workspace/a workspace/b workspace/c
  $ cat > workspace/a/dune <<'EOF'
  > (rocq.theory
  >  (name a)
  >  (theories b c))
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
  $ env -u DUNE_ROOT DUNE_SOURCEROOT="$test_root/workspace" "$tool"
  $ cat dune
  (rocq.theory
   (name a)
   (theories b c))
