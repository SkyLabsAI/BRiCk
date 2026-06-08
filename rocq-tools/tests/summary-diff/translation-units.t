  $ cat > base.csv <<EOF
  > File,instructions
  > tu_cpp.v,10000000000
  > proof,20000000000
  > EOF

  $ cat > job.csv <<EOF
  > File,instructions
  > tu_cpp.v,15000000000
  > proof,25000000000
  > EOF

  $ rocq-perf.summary-diff --no-colors --instr-threshold 0 --markdown base.csv job.csv
  | Relative | Master   | MR       | Change   | Filename
  |---------:|---------:|---------:|---------:|----------
  |  +25.00% |     20.0 |     25.0 |     +5.0 | proof
  |  +50.00% |     10.0 |     15.0 |     +5.0 | tu_cpp.v
  |  +33.33% |     30.0 |     40.0 |    +10.0 | total
  |  +50.00% |     10.0 |     15.0 |     +5.0 | ├ translation units
  |  +25.00% |     20.0 |     25.0 |     +5.0 | └ proofs and tests
