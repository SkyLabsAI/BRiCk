Noise-free examples for every model described in the README are classified as
that model by the command-line estimator, including higher-degree polynomial and
quasi-polynomial models.

  $ python3 - <<'PY'
  > import math
  > cases = {
  >     "constant": ([1, 2, 4, 8, 16, 32, 64], lambda n: 5.0),
  >     "logarithmic": ([1, 2, 4, 8, 16, 32, 64], lambda n: 1.0 + 2.0 * math.log(n)),
  >     "linear": ([1, 2, 4, 8, 16, 32, 64], lambda n: 1.0 + 2.0 * n),
  >     "linearithmic": ([2, 4, 8, 16, 32, 64, 128, 256], lambda n: 1.0 + 2.0 * n * math.log(n)),
  >     "quadratic-log": (range(2, 12), lambda n: 1.0 + 0.5 * n + 0.25 * n * n * math.log(n)),
  >     "polynomial": ([1, 2, 4, 8, 16, 32, 64], lambda n: 1.0 + 0.5 * n + 0.25 * n * n),
  >     "centered-quadratic": (range(1, 10), lambda n: (n - 5) ** 2 + 1.0),
  >     "cubic": (range(1, 10), lambda n: 1.0 + 0.5 * n + 0.25 * n * n + 0.125 * n * n * n),
  >     "quartic": (range(1, 12), lambda n: 1.0 + 2.0 * n + 3.0 * n ** 2 + 0.5 * n ** 3 + 0.05 * n ** 4),
  >     "powerlaw": ([1, 2, 4, 8, 16, 32, 64], lambda n: 3.0 * (n ** 1.7)),
  >     "exponential": (range(1, 9), lambda n: 2.0 * math.exp(0.25 * n)),
  > }
  > for name, (xs, f) in cases.items():
  >     with open(f"{name}.csv", "w") as out:
  >         out.write("n,time\n")
  >         for n in xs:
  >             out.write(f"{n},{f(n):.17g}\n")
  > PY

  $ for case in constant logarithmic linear linearithmic quadratic-log polynomial centered-quadratic cubic quartic powerlaw exponential; do
  >   best=$(guesstimator fit --normalize-samples=false "$case.csv" | awk -F': ' '/Best by BIC/ {print $2}')
  >   printf '%-12s -> %s\n' "$case" "$best"
  > done
  constant     -> constant
  logarithmic  -> logarithmic
  linear       -> polynomial-1
  linearithmic -> quasi-polynomial-1
  quadratic-log -> quasi-polynomial-2
  polynomial   -> polynomial-2
  centered-quadratic -> polynomial-2
  cubic        -> polynomial-3
  quartic      -> polynomial-4
  powerlaw     -> power-law
  exponential  -> exponential
