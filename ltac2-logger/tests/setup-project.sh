cat > dune <<EOF
(rocq.theory
 (name test)
 (theories Stdlib Ltac2 skylabs.ltac2.extra skylabs.ltac2.logger))
EOF

cat > dune-project <<EOF
(lang dune 3.21)
(using rocq 0.11)
EOF

export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
export PATH="$DUNE_SOURCEROOT/_build/install/default/bin:$PATH"
export DUNE_CACHE=disabled
