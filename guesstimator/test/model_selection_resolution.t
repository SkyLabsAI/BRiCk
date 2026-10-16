Model-selection resolution distinguishes statistical detectability from a
material change in dominant growth class. The two motivating traces are linear
at the default one-part-per-million resolution.

  $ for f in linear-resolution-1.csv linear-resolution-2.csv; do
  >   guesstimator fit "inputs/$f" |
  >     awk -v f="$f" -F': ' '/Model-selection resolution/ {r=$2} /Best by BIC/ {print f, "resolution=" r, "best=" $2}'
  > done
  linear-resolution-1.csv resolution=1e-06 best=polynomial-1
  linear-resolution-2.csv resolution=1e-06 best=polynomial-1

The richer quadratic remains statistically detectable, but its complete
model-based effect interval is below the declared resolution.

  $ guesstimator fit --print-comparisons=within inputs/linear-resolution-2.csv |
  >   awk '/polynomial-1[[:space:]]+vs polynomial-2/ {print $1, $2, $3, $4, $5, $6, $7; getline; print $1, $2, $3, $4}'
  polynomial-1 vs polynomial-2 -> polynomial-1 (F,p)=(17.237,7.0946e-05) significant=yes
  relative-effect=4.027e-07 95.0%-CI=[2.102e-07,5.951e-07] resolution=1e-06 materiality=equivalent

Zero resolution is the compatibility mode for the old nested F-test behavior.

  $ for f in linear-resolution-1.csv linear-resolution-2.csv; do
  >   guesstimator fit --model-selection-resolution=0 "inputs/$f" |
  >     awk -v f="$f" -F': ' '/Best by BIC/ {print f, $2}'
  > done
  linear-resolution-1.csv quasi-polynomial-5
  linear-resolution-2.csv quasi-polynomial-11

Fit and assert use the same materiality policy, and forced high degrees cannot
redefine the normal best.

  $ guesstimator assert polynomial-1 inputs/linear-resolution-1.csv
  $ guesstimator assert polynomial-1 inputs/linear-resolution-2.csv
  $ guesstimator assert quasi-polynomial-5 inputs/linear-resolution-1.csv
  [1]
  $ guesstimator assert quasi-polynomial-11 inputs/linear-resolution-2.csv
  [1]
  $ guesstimator assert --model-selection-resolution=0 quasi-polynomial-5 inputs/linear-resolution-1.csv
  $ guesstimator assert --model-selection-resolution=0 quasi-polynomial-11 inputs/linear-resolution-2.csv

Both subcommands document the policy option.

  $ guesstimator fit --help=plain | grep -o -- '--model-selection-resolution' | head -1
  --model-selection-resolution
  $ guesstimator assert --help=plain | grep -o -- '--model-selection-resolution' | head -1
  --model-selection-resolution

Resolution validation happens before input access and uses the repository's
invalid-command-line status.

  $ guesstimator fit --model-selection-resolution=2 does-not-exist.csv 2>&1
  guesstimator: model-selection resolution must be a finite number between 0 and 1
  [102]
  $ guesstimator fit --model-selection-resolution=nan does-not-exist.csv 2>&1
  guesstimator: model-selection resolution must be a finite number between 0 and 1
  [102]
  $ guesstimator assert --model-selection-resolution=-1 polynomial-1 does-not-exist.csv 2>&1
  guesstimator: model-selection resolution must be a finite number between 0 and 1
  [102]

Holdout reruns receive the same resolution as the full-data selector.

  $ guesstimator fit --holdout inputs/linear-resolution-2.csv |
  >   grep -E '^(Best by BIC|  Stability)'
  Best by BIC: polynomial-1
    Stability for polynomial-1: 100.0% (5/5, threshold 80.0%) stable
  $ guesstimator fit --model-selection-resolution=0 --holdout inputs/linear-resolution-2.csv |
  >   grep -E '^(Best by BIC|  Stability)'
  Best by BIC: quasi-polynomial-11 (WARNING: holdout stability suspiciously low at 60.0% < 80.0%)
    Stability for quasi-polynomial-11: 60.0% (3/5, threshold 80.0%) unstable
