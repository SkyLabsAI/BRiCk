Concrete CSV fixtures under test/inputs are classified as their expected
complexity classes.

  $ for case in constant logarithmic polynomial power-law exponential; do
  >   best=$(guesstimator fit "inputs/$case.csv" | awk -F': ' '/Best by BIC/ {print $2}')
  >   printf '%-12s -> %s\n' "$case" "$best"
  > done
  constant     -> constant
  logarithmic  -> logarithmic
  polynomial   -> polynomial-2
  power-law    -> power-law
  exponential  -> exponential

Comparison printing is opt-in. Within-class comparison output includes polynomial
degree choices, while all-mode also includes across-class comparisons under a
separate heading.

  $ if guesstimator fit inputs/polynomial.csv | grep -q 'class comparisons'; then echo unexpected; else echo 'no comparisons by default'; fi
  no comparisons by default

  $ guesstimator fit --print-comparisons=within inputs/polynomial.csv | awk '/Within-class comparisons/ {print}; /polynomial-1[[:space:]]+vs polynomial-2/ {print $1, $2, $3, $4, $5, $NF}; /Across-class comparisons/ {print}'
  Within-class comparisons (nested F test where applicable, otherwise BIC):
  polynomial-1 vs polynomial-2 -> polynomial-2 significant=yes

  $ guesstimator fit --print-comparisons=all inputs/polynomial.csv | grep 'class comparisons'
  Within-class comparisons (nested F test where applicable, otherwise BIC):
  Across-class comparisons (nested F test where applicable, otherwise BIC):

Loser-fit printing is independently opt-in. It reports full statistics for
compared losers that are not already in Fits, including losers of internal
selection comparisons. It neither prints comparison details nor fits untested
higher degrees.

  $ if guesstimator fit inputs/polynomial.csv | grep -q '^Comparison loser fits'; then echo unexpected; else echo 'no loser fits by default'; fi
  no loser fits by default

  $ guesstimator fit --print-loser-fits inputs/polynomial.csv | awk '/^Comparison loser fits/ { printing=1; print; next } printing && /^  / { print $1, $2, $4, $6, $8 }'
  Comparison loser fits (not already listed under Fits):
  polynomial-3 RSS= R^2= AIC= BIC=
  quasi-polynomial-2 RSS= R^2= AIC= BIC=
  polynomial-1 RSS= R^2= AIC= BIC=
  quasi-polynomial-1 RSS= R^2= AIC= BIC=

  $ guesstimator fit --print-loser-fits inputs/polynomial.csv | awk '/^  polynomial-2[[:space:]]+RSS=/ { count++ } END { print "polynomial-2 rows:", count }'
  polynomial-2 rows: 1

  $ if guesstimator fit --print-loser-fits inputs/polynomial.csv | grep -q 'class comparisons'; then echo unexpected; else echo 'loser fits are independent'; fi
  loser fits are independent
