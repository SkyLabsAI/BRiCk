cat > dune <<EOF
(rocq.theory
 (name test)
 (theories Stdlib tc_db_info))
EOF

cat > dune-project <<EOF
(lang dune 3.21)
(using rocq 0.11)
EOF

export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
export DUNE_CACHE=disabled
