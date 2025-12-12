cat > dune <<EOF
(coq.theory
 (name test)
 (theories Lens Lens.Elpi elpi elpi_elpi elpi.apps.derive Stdlib stdpp Ltac2 bluerock.ltac2.extra bluerock.upoly bluerock.prelude))
EOF

cat > dune-project <<EOF
(lang dune 3.8)
(using coq 0.8)
EOF

export ROCQPATH="$DUNE_SOURCEROOT/_build/install/default/lib/coq/user-contrib"
export ROCQLIB="$DUNE_SOURCEROOT/_build/install/default/lib/coq"
export DUNE_CACHE=disabled
