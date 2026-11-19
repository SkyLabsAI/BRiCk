CSV input handling promised by the binary: optional headers, forced header
policy, and stdin via `-`.

  $ cat > with-header.csv <<'EOF'
  > n,time
  > 1,5
  > 2,5
  > 3,5
  > 4,5
  > EOF
  $ cat > without-header.csv <<'EOF'
  > 1,5
  > 2,5
  > 3,5
  > 4,5
  > EOF

  $ guesstimator fit with-header.csv | grep -E '^(Header|Observations|Best by BIC):'
  Header: yes
  Observations: 4
  Best by BIC: constant

  $ guesstimator fit without-header.csv | grep -E '^(Header|Observations|Best by BIC):'
  Header: no
  Observations: 4
  Best by BIC: constant

  $ guesstimator fit --header=true with-header.csv | grep -E '^(Header|Observations|Best by BIC):'
  Header: yes
  Observations: 4
  Best by BIC: constant

  $ guesstimator fit --header=false without-header.csv | grep -E '^(Header|Observations|Best by BIC):'
  Header: no
  Observations: 4
  Best by BIC: constant

  $ guesstimator fit --header=true without-header.csv 2>&1
  guesstimator: --header=true was specified, but CSV row 1 contains two numeric values and looks like data
  [123]

  $ guesstimator fit --header=false with-header.csv 2>&1
  guesstimator: --header=false was specified, but CSV row 1 does not contain two numeric values
  [123]

  $ cat with-header.csv | guesstimator fit - | grep -E '^(Input|Header|Best by BIC):'
  Input: -
  Header: yes
  Best by BIC: constant

Verbose mode includes comparison rationale notes when comparison printing is enabled.

  $ guesstimator fit --print-comparisons=across --verbose with-header.csv | grep -m 1 '^    note:'
      note: richer model does not numerically reduce residual error; simpler model selected
