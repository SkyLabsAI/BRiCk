cat > dune <<EOF
(rocq.theory
 (name test)
 (theories Lens Lens.Elpi elpi elpi_elpi elpi.apps.derive Stdlib stdpp Ltac2 skylabs.ltac2.extra skylabs.upoly skylabs.prelude))
EOF

cat > dune-project <<EOF
(lang dune 3.21)
(using rocq 0.11)
EOF

export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
export DUNE_CACHE=disabled
