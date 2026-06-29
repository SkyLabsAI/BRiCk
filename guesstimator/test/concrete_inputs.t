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
