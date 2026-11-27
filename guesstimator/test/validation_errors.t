Input validation rejects malformed CSV and observations outside the advertised
finite-positive domain.

  $ touch empty.csv
  $ guesstimator fit empty.csv 2>&1
  guesstimator: CSV file is empty
  [123]

  $ cat > wrong-columns.csv <<'EOF'
  > n,time,extra
  > 1,2,3
  > EOF
  $ guesstimator fit wrong-columns.csv 2>&1
  guesstimator: CSV row 1 has 3 columns; expected exactly 2
  [123]

  $ cat > not-a-number.csv <<'EOF'
  > n,time
  > 1,2
  > oops,3
  > 3,4
  > EOF
  $ guesstimator fit not-a-number.csv 2>&1
  guesstimator: CSV row 3, column 1 is not a number: "oops"
  [123]

  $ cat > too-few.csv <<'EOF'
  > n,time
  > 1,2
  > 2,4
  > EOF
  $ guesstimator fit too-few.csv 2>&1
  guesstimator: constant: need at least three observations
  [123]

  $ cat > non-positive.csv <<'EOF'
  > n,time
  > 1,2
  > 2,0
  > 3,4
  > EOF
  $ guesstimator fit non-positive.csv 2>&1
  guesstimator: constant: all problem sizes and times must be finite positive numbers
  [123]

Holdout tuning options are invalid when the mode they configure is disabled.
They use a dedicated command-line argument error status and are validated before
reading the input file.

  $ guesstimator fit --holdout-folds=3 does-not-exist.csv 2>&1
  guesstimator: --holdout-folds requires --holdout
  [102]

  $ guesstimator assert --holdout-tail-fraction=0.5 constant does-not-exist.csv 2>&1
  guesstimator: --holdout-tail-fraction requires --holdout-tail
  [102]

  $ guesstimator fit --holdout-stability-threshold=0.5 does-not-exist.csv 2>&1
  guesstimator: --holdout-stability-threshold requires --holdout or --holdout-tail
  [102]

The tuning options remain valid when their corresponding modes are enabled.

  $ guesstimator assert --holdout --holdout-folds=2 --holdout-stability-threshold=0 constant inputs/constant.csv

  $ guesstimator assert --holdout-tail --holdout-tail-fraction=0.5 --holdout-stability-threshold=0 constant inputs/constant.csv
