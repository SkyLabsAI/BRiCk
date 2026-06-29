The assert subcommand checks the requested class without printing output. It exits
0 when the class is the best retained fit or is within the allowed BIC delta, and
1 when it is not.

Assertions succeed for all model families accepted by CLASS.

  $ guesstimator assert constant inputs/constant.csv

  $ guesstimator assert logarithmic inputs/logarithmic.csv

  $ guesstimator assert polynomial-2 inputs/polynomial.csv

  $ guesstimator assert power-law inputs/power-law.csv

  $ guesstimator assert exponential inputs/exponential.csv

  $ python3 - <<'PY'
  > import math
  > with open('quasi-polynomial.csv', 'w') as out:
  >     out.write('n,time\n')
  >     for n in [2, 4, 8, 16, 32, 64, 128, 256]:
  >         out.write(f'{n},{1.0 + 2.0 * n * math.log(n):.17g}\n')
  > PY
  $ guesstimator assert --normalize-samples=false quasi-polynomial-1 quasi-polynomial.csv

Near-ties within the default `--max-delta-bic=2` threshold are accepted, while a
zero threshold restores strict best-fit matching.

  $ guesstimator assert power-law inputs/constant.csv

  $ guesstimator assert --max-delta-bic=0 power-law inputs/constant.csv
  [1]

Assert includes the requested polynomial degree in the candidate set even when
the normal degree search would prune it from `fit` output.

  $ cat > pruned-quartic.csv <<'EOF'
  > n,time
  > 1,82
  > 2,17
  > 3,2
  > 4,1
  > 5,2
  > 6,17
  > 7,82
  > EOF
  $ guesstimator fit --normalize-samples=false pruned-quartic.csv | grep 'Best by BIC'
  Best by BIC: polynomial-2 (WARNING: RSME suspiciously high at 27.7% > 20%)
  $ if guesstimator fit --normalize-samples=false pruned-quartic.csv | grep -q '^  polynomial-4'; then echo unexpected; else echo 'polynomial-4 not retained by default'; fi
  polynomial-4 not retained by default
  $ guesstimator assert --normalize-samples=false polynomial-4 pruned-quartic.csv

A mismatch outside the BIC threshold exits with status 1 and still prints nothing.

  $ guesstimator assert logarithmic inputs/polynomial.csv
  [1]

The holdout options check whether model selection remains stable across grouped
problem-size holdouts. This data succeeds without holdouts but fails the default
80% stability threshold with round-robin holdouts.

  $ cat > unstable-holdout.csv <<'EOF'
  > n,time
  > 1,3.33613067297
  > 2,3.85770798195
  > 3,10.842686828
  > 4,8.15447003202
  > 5,14.9115841323
  > 6,20.2378213756
  > 7,31.4383168829
  > 8,33.6493639664
  > 9,43.33871474
  > EOF
  $ guesstimator assert --normalize-samples=false power-law unstable-holdout.csv

  $ guesstimator assert --normalize-samples=false --holdout power-law unstable-holdout.csv
  [101]

  $ guesstimator assert --normalize-samples=false --holdout --holdout-stability-threshold=0.6 power-law unstable-holdout.csv

  $ guesstimator fit --normalize-samples=false --holdout unstable-holdout.csv | grep -E 'Hold-out|Stability|median relative RSME|power-law'
  Best by BIC: power-law (WARNING: holdout stability suspiciously low at 60.0% < 80.0%)
    power-law     RSS=     46.63  R^2= 0.9715  AIC=   18.804  BIC=   19.199  coefficient=1.1199, log_coefficient=0.11328, exponent=1.6582
  Hold-out validation (5-fold round-robin by problem size):
    Stability for power-law: 60.0% (3/5, threshold 80.0%) unstable
    Class                   runs median relative RSME    max relative RSME
    power-law                3/5                16.5%                17.2%

Tail holdout can be enabled separately.

  $ guesstimator assert --holdout-tail polynomial-2 inputs/polynomial.csv

  $ guesstimator fit --holdout-tail inputs/polynomial.csv | grep -E 'Tail hold-out|Stability|median relative RSME'
  Tail hold-out validation (largest 25.0% of problem sizes):
    Stability for polynomial-2: 100.0% (1/1, threshold 80.0%) stable
    Class                   runs median relative RSME    max relative RSME

A high relative RSME makes the best fit suspicious. The fit command warns on the
Best by BIC line, while assert exits 100 even if CLASS matches the suspicious
best fit.

  $ cat > suspicious.csv <<'EOF'
  > n,time
  > 1,1
  > 2,100
  > 3,1
  > 4,100
  > 5,1
  > 6,100
  > 7,1
  > 8,100
  > EOF
  $ guesstimator fit suspicious.csv | grep 'Best by BIC'
  Best by BIC: constant (WARNING: RSME suspiciously high at 98.0% > 20%)
  $ guesstimator assert constant suspicious.csv
  [100]

  $ guesstimator assert --help=plain | grep -A1 '100 the best fit' | sed 's/^ *//'
  100 the best fit is suspicious because relative RSME is greater than
  20%
  $ guesstimator assert --help=plain | grep '101 hold-out' | sed 's/^ *//'
  101 hold-out validation did not reach the stability threshold

It shares header handling and holdout options with fit, but not fit-only output options.

  $ guesstimator assert --header=true constant inputs/constant.csv

  $ cat > constant-no-header.csv <<'EOF'
  > 1,5
  > 2,5
  > 4,5
  > 8,5
  > EOF
  $ guesstimator assert --header=false constant constant-no-header.csv

  $ cat inputs/constant.csv | guesstimator assert constant -

  $ sh -c 'err=$(mktemp); TERM=dumb guesstimator assert --print-comparisons=all constant inputs/constant.csv >"$err" 2>&1; status=$?; echo exit:$status; grep -o "unknown option '\''--print-comparisons'\''" "$err"; rm -f "$err"'
  exit:124
  unknown option '--print-comparisons'

CLASS is parsed with the canonical complexity parser. Unknown classes report the
accepted names, using -N for degree-bearing classes.

  $ sh -c 'err=$(mktemp); TERM=dumb guesstimator assert nope inputs/constant.csv >"$err" 2>&1; status=$?; echo exit:$status; grep -o "unknown complexity class: \"nope\"; expected one" "$err"; grep -o "of: constant, logarithmic, polynomial-N, quasi-polynomial-N," "$err"; grep -o "power-law, exponential" "$err"; rm -f "$err"'
  exit:124
  unknown complexity class: "nope"; expected one
  of: constant, logarithmic, polynomial-N, quasi-polynomial-N,
  power-law, exponential

  $ sh -c 'err=$(mktemp); TERM=dumb guesstimator assert polynomial-0 inputs/constant.csv >"$err" 2>&1; status=$?; echo exit:$status; grep -o "polynomial-N" "$err" | head -1; rm -f "$err"'
  exit:124
  polynomial-N
