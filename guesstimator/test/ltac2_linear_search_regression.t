Ltac2 instruction-counter data from an attempted unsorted-list linear search
complexity test. The final measurement includes a large outlier, so the best BIC
model is not the linear model and a strict linear assertion fails; a sufficiently
large BIC delta still accepts the linear model as a plausible explanation.

  $ cat > ltac2-linear-search-instructions.csv <<'EOF'
  > n,time
  > 16,3654716
  > 24,5094394
  > 32,6533884
  > 48,9412801
  > 64,12291627
  > 96,18049791
  > 128,23807739
  > 192,35323646
  > 256,49670374
  > 384,69871364
  > 512,129495715
  > EOF

  $ guesstimator fit ltac2-linear-search-instructions.csv | awk -F': ' '/Best by BIC/ {print $2}'
  quasi-polynomial-9

  $ guesstimator assert --max-delta-bic=10 polynomial-1 ltac2-linear-search-instructions.csv
  [1]

  $ guesstimator assert --max-delta-bic=250 polynomial-1 ltac2-linear-search-instructions.csv
