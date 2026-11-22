export DUNE_CACHE=disabled
export PATH="$(dirname "$DUNE"):$PATH"
export OCAMLPATH="${OCAMLPATH%%:*}"
unset DUNE_ACTION_TRACE_DIR
export LC_ALL=C
