  $ test_root=$(mktemp -d "${TMPDIR:-/tmp}/rocq-dune-tools-file-ops.XXXXXX")
  $ cd "$test_root"
  $ cat > dune-project <<'EOF'
  > (lang dune 3.21)
  > (name cram_file_ops)
  > (using rocq 0.11)
  > EOF
  $ mkdir -p workspace/pkg workspace/fmdeps/cpp2v-core/rocq-skylabs-brick/tests
  $ cat > workspace/pkg/dune <<'EOF'
  > (rocq.theory
  >  (name smoke.pkg))
  > EOF

  $ dune-rocqproject --root workspace/missing 2>&1 | sed -n '1p'
  error: workspace/missing/ is not a directory

  $ dune-rocqproject generate-coq-project 2>&1 | sed -n '3p'
  dune-rocqproject: too many arguments, don't know what to do with

  $ dune-rocqproject gather-coq-paths 2>&1 | sed -n '3p'
  dune-rocqproject: too many arguments, don't know what to do with

  $ bad_root=$(mktemp -d "${TMPDIR:-/tmp}/rocq-dune-tools-bad.XXXXXX")
  $ cd "$bad_root"
  $ cat > dune-project <<'EOF'
  > (lang dune 3.21)
  > (name cram_bad)
  > (using rocq 0.11)
  > EOF
  $ mkdir -p bad
  $ cat > bad/dune <<'EOF'
  > (rocq.theory
  >  (name broken)
  > EOF
  $ dune-rocqproject --root . 2>&1 | grep "unclosed parenthesis at end of input"
  Error: unclosed parenthesis at end of input
  $ cd "$test_root"

  $ dune-rocqproject --root workspace --coq-flags absent.flags
  # AUTO-GENERATED CONTENT, EDIT `dune-rocqproject` INSTEAD
  
  # Avoid warnings about entries in this _CoqProject
  -arg -w -arg -cannot-open-path
  
  # Plugin directory.
  -I _build/install/default/lib
  
  # Specified logical paths for directories (for .v and .vo files).
  -Q _build/default/workspace/pkg/ smoke.pkg
  -Q workspace/pkg/ smoke.pkg
  -Q fmdeps/cpp2v-core/rocq-skylabs-brick/tests/ bedrocktest
  -Q _build/default/fmdeps/cpp2v-core/rocq-skylabs-brick/tests/ bedrocktest

  $ DUNE_BUILD_DIR=altbuild dune-rocqproject --root workspace | grep '^-Q'
  -Q altbuild/default/workspace/pkg/ smoke.pkg
  -Q workspace/pkg/ smoke.pkg
  -Q fmdeps/cpp2v-core/rocq-skylabs-brick/tests/ bedrocktest
  -Q altbuild/default/fmdeps/cpp2v-core/rocq-skylabs-brick/tests/ bedrocktest

  $ cd workspace/pkg
  $ dune-rocqproject | grep '^-Q'
  -Q ../../_build/default/workspace/pkg/ smoke.pkg
  -Q ./ smoke.pkg
