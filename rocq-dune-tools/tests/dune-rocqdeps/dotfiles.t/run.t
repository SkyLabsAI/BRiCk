  $ test_root=$(mktemp -d "${TMPDIR:-/tmp}/dune-rocqdeps-dotfiles.XXXXXX")
  $ tool="$(command -v dune-rocqdeps)"
  $ cd "$test_root"
  $ cat > dune-project <<'EOF'
  > (lang dune 3.22)
  > (name cram_dune_rocqdeps_dotfiles)
  > (using rocq 0.12)
  > EOF
  $ mkdir -p lib
  $ cat > lib/dune <<'EOF'
  > (rocq.theory
  >  (name lib))
  > EOF
  $ ln -s missing-host:12345 lib/.#helpers.v
  $ env -u DUNE_SOURCEROOT -u DUNE_ROOT "$tool"
  $ cat lib/dune
  (rocq.theory
   (name lib))
