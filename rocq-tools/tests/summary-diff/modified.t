  $ cat > base.csv <<EOF
  > File,instructions
  > a,2000000000
  > b,4000000000
  > c,8000000000
  > d,16000000000
  > EOF

  $ cat > job.csv <<EOF
  > File,instructions
  > a,2000000000
  > b,4000000000
  > c,16000000000
  > d,32000000000
  > EOF

  $ rocq-perf.summary-diff --no-colors --instr-threshold 0 --markdown base.csv job.csv
  | Relative | Master   | MR       | Change   | Filename
  |---------:|---------:|---------:|---------:|----------
  | +100.00% |      8.0 |     16.0 |     +8.0 | c
  | +100.00% |     16.0 |     32.0 |    +16.0 | d
  |  +80.00% |     30.0 |     54.0 |    +24.0 | total
  |  +80.00% |     30.0 |     54.0 |    +24.0 | └ proofs and tests
