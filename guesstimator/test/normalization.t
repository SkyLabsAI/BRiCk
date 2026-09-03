The CLI normalizes problem sizes by default and exposes a boolean opt-out.

  $ cat > linear-scale.csv <<'EOF'
  > n,time
  > 1,3
  > 2,5
  > 3,7
  > 4,9
  > EOF

  $ guesstimator fit --help=plain | grep -o -- '--normalize-samples' | head -1
  --normalize-samples

  $ guesstimator fit --help=plain | grep -o -- '--fit-parameter-scale' | head -1
  --fit-parameter-scale

  $ guesstimator fit --help=plain | awk '/--fit-parameter-scale/ {seen=1} seen && /original/ && /normalized/ {print "fit parameter scale choices documented"; exit}'
  fit parameter scale choices documented

  $ guesstimator assert --help=plain | grep -o -- '--normalize-samples' | head -1
  --normalize-samples

Default mode normalizes samples for fitting but prints parameters in the original
input problem-size scale.

  $ guesstimator fit linear-scale.csv | awk '/^Normalized samples:/ {print}; /^Fit parameter scale:/ {print}; /^  polynomial-1[[:space:]]+RSS=/ {print $1, $NF}'
  Normalized samples: yes
  Fit parameter scale: original problem size
  polynomial-1 linear=2

  $ guesstimator fit --normalize-samples=true linear-scale.csv | awk '/^Normalized samples:/ {print}; /^Fit parameter scale:/ {print}; /^  polynomial-1[[:space:]]+RSS=/ {print $1, $NF}'
  Normalized samples: yes
  Fit parameter scale: original problem size
  polynomial-1 linear=2

Explicit normalized parameter display exposes the fitted coordinate.

  $ guesstimator fit --fit-parameter-scale=normalized linear-scale.csv | awk '/^Normalized samples:/ {print}; /^Fit parameter scale:/ {print}; /^  polynomial-1[[:space:]]+RSS=/ {print $1, $NF}'
  Normalized samples: yes
  Fit parameter scale: normalized problem size
  polynomial-1 linear=8

Disabling normalization restores raw problem-size fitting and is accepted by both
subcommands.

  $ guesstimator fit --normalize-samples=false linear-scale.csv | awk '/^Normalized samples:/ {print}; /^Fit parameter scale:/ {print}; /^  polynomial-1[[:space:]]+RSS=/ {print $1, $NF}'
  Normalized samples: no
  Fit parameter scale: input problem size
  polynomial-1 linear=2

  $ guesstimator assert --normalize-samples=false polynomial-1 linear-scale.csv
