Regression tests for statistical bugs found during review.

Power-law and exponential regressions are optimized and ranked on the same
original-time RSS/BIC scale. This input used to select a polynomial because the
exponential parameters were fitted in log space; it now selects the better
time-scale exponential fit.

  $ cat > log-space-ranking.csv <<'EOF'
  > n,time
  > 1,2.04872127
  > 2,2.31828183
  > 3,4.88168907
  > 4,6.98905610
  > 5,12.58249396
  > EOF
  $ guesstimator fit --normalize-samples=false log-space-ranking.csv | awk '/Best by BIC/ {print}; /^  polynomial-2[[:space:]]+RSS=/ {print $1, $2, $3}; /^  exponential[[:space:]]+RSS=/ {print $1, $2, $3}'
  Best by BIC: exponential
  exponential RSS= 0.7348
  polynomial-2 RSS= 0.7819
  $ python3 - <<'PY'
  > import math
  > xs = [1, 2, 3, 4, 5]
  > ys = [2.04872127, 2.31828183, 4.88168907, 6.98905610, 12.58249396]
  > def rss_for(k):
  >     zs = [math.exp(k * x) for x in xs]
  >     c = sum(y * z for y, z in zip(ys, zs)) / sum(z * z for z in zs)
  >     return sum((y - c * z) ** 2 for y, z in zip(ys, zs))
  > a, b = -1.0, 2.0
  > gr = (math.sqrt(5.0) - 1.0) / 2.0
  > c = b - gr * (b - a)
  > d = a + gr * (b - a)
  > fc = rss_for(c)
  > fd = rss_for(d)
  > for _ in range(120):
  >     if fc > fd:
  >         a, c, fc = c, d, fd
  >         d = a + gr * (b - a)
  >         fd = rss_for(d)
  >     else:
  >         b, d, fd = d, c, fc
  >         c = b - gr * (b - a)
  >         fc = rss_for(c)
  > rss = rss_for((a + b) / 2.0)
  > bic = len(xs) * math.log(rss / len(xs)) + 2.0 * math.log(len(xs))
  > print(f"time-scale exponential RSS={rss:.4f} BIC={bic:.4f}")
  > PY
  time-scale exponential RSS=0.7348 BIC=-6.3694

Pairwise comparisons use F-tests only for nested models. On this input, BIC now
picks the searched cubic polynomial, and the non-nested polynomial-vs-power-law
comparison still does not run a significance test.

  $ python3 - <<'PY'
  > import math
  > with open('non-nested-f-test.csv', 'w') as out:
  >     out.write('n,time\n')
  >     for n in range(1, 61):
  >         t = 100 + 4.9378446115 * (((n - 30.5) / 60) ** 2 - 3599 / 43200) + 1.0542168675 * math.sin(0.2 * n)
  >         out.write(f'{n},{t:.12f}\n')
  > PY
  $ guesstimator fit --normalize-samples=false --print-comparisons=across non-nested-f-test.csv | awk '/Best by BIC/ {print}; /polynomial-3[[:space:]]+vs power-law/ {print $1, $2, $3, $4, $5, $6, $7}'
  Best by BIC: polynomial-3
  polynomial-3 vs power-law -> polynomial-3 (F,p)=n/a significant=no

A power-law case also locks coverage for original-time nonlinear fitting. The old
log-log fit had RSS around 2.2e6 on this input; the fixed time-scale power-law
fit still has much lower RSS, even though the searched cubic polynomial now wins
by BIC on this finite noisy sample.

  $ cat > power-time-scale.csv <<'EOF'
  > n,time
  > 1,10.971051
  > 2,12.661027
  > 4,15.647589
  > 8,11.634113
  > 16,133.433716
  > 32,329.746835
  > 64,1215.007865
  > 128,3484.142757
  > EOF
  $ guesstimator fit --normalize-samples=false power-time-scale.csv | awk '/Best by BIC/ {print}; /^  power-law[[:space:]]+RSS=/ {print $1, $2, $3}; /^  polynomial-3[[:space:]]+RSS=/ {print $1, $2, $3}'
  Best by BIC: polynomial-3
  polynomial-3 RSS= 2037
  power-law RSS= 7164

Exact constant observations should prefer the simpler constant model, even
though zero-slope power-law and exponential models are mathematically equivalent.
This protects against a roundoff/tie-breaking caveat where nonlinear
zero-residual fits could outrank the constant fit because the constant
regression left a tiny roundoff residual.

  $ cat > exact-constant-linear.csv <<'EOF'
  > n,time
  > 1,1
  > 2,1
  > 3,1
  > 4,1
  > 5,1
  > 6,1
  > 7,1
  > 8,1
  > EOF
  $ guesstimator fit exact-constant-linear.csv | awk -F': ' '/Best by BIC/ {print $2}'
  constant
  $ guesstimator fit --normalize-samples=false exact-constant-linear.csv | awk -F': ' '/Best by BIC/ {print $2}'
  constant
  $ guesstimator assert constant exact-constant-linear.csv

The same preference should hold for exact constant observations on a geometric
problem-size grid.

  $ cat > exact-constant-geometric.csv <<'EOF'
  > n,time
  > 1,1
  > 2,1
  > 4,1
  > 8,1
  > 16,1
  > 32,1
  > 64,1
  > 128,1
  > EOF
  $ guesstimator fit exact-constant-geometric.csv | awk -F': ' '/Best by BIC/ {print $2}'
  constant

Exact or numerically near-exact richer fits produce p=0 instead of NaN, so the
nested pairwise comparison selects the richer model without treating finite
roundoff residuals as literally zero.

  $ cat > exact-richer.csv <<'EOF'
  > n,time
  > 1,2
  > 2,5
  > 3,10
  > 4,17
  > EOF
  $ guesstimator fit --normalize-samples=false --print-comparisons=across exact-richer.csv | awk '/Best by BIC/ {print}; /constant[[:space:]]+vs polynomial-2/ {pair=$6; sub(/^\(F,p\)=\(/, "", pair); sub(/\)$/, "", pair); split(pair, parts, ","); printf "%s %s %s %s %s (F,p)=(%s,%s)\n", $1, $2, $3, $4, $5, (parts[1] == "inf" ? "inf" : "finite"), parts[2]}'
  Best by BIC: polynomial-2
  constant vs polynomial-2 -> polynomial-2 (F,p)=(finite,0)

The polynomial degree search does not let a weak linear/quadratic prefix hide a
higher-degree polynomial. The same data scaled to small time units is classified
the same way.

  $ cat > hidden-cubic.csv <<'EOF'
  > n,time
  > 1,1
  > 2,3
  > 3,3
  > 4,7
  > 5,21
  > EOF
  $ guesstimator fit --normalize-samples=false hidden-cubic.csv | awk -F': ' '/Best by BIC/ {print $2}'
  polynomial-3
  $ python3 - <<'PY'
  > with open('hidden-cubic-small.csv', 'w') as out:
  >     out.write('n,time\n')
  >     for n, t in [(1, 1), (2, 3), (3, 3), (4, 7), (5, 21)]:
  >         out.write(f'{n},{t * 1e-9:.17g}\n')
  > PY
  $ guesstimator fit --normalize-samples=false hidden-cubic-small.csv | awk -F': ' '/Best by BIC/ {print $2}'
  polynomial-3

The nonlinear slope search uses a broad grid plus local refinement, so it does
not stop at a poor one-sided bracket.

  $ cat > nonlinear-search.csv <<'EOF'
  > n,time
  > 1,40.35105755137664
  > 2,0.2693556159897494
  > 3,8.758890089379172
  > 4,29.94111029566006
  > EOF
  $ guesstimator fit --normalize-samples=false nonlinear-search.csv | awk '/^  exponential[[:space:]]+RSS=/ {print $1, $2, $3, $NF}'
  exponential RSS= 958.3 rate=-0.34643

Large-offset exact exponentials still fit as exponentials; centering the initial
linearized regression avoids falsely declaring the design rank-deficient.

  $ python3 - <<'PY'
  > import math
  > start = 1_000_000_000_000
  > with open('large-offset-exponential.csv', 'w') as out:
  >     out.write('n,time\n')
  >     for i in range(5):
  >         n = start + i
  >         out.write(f'{n},{math.exp(i):.17g}\n')
  > PY
  $ guesstimator fit --normalize-samples=false large-offset-exponential.csv | awk '/^  exponential[[:space:]]+RSS=/ {print $1, $2, $3, $NF}'
  exponential RSS= 0 rate=1

Three observations are not enough to rank a three-parameter quadratic model; the
polynomial search stops before saturated fits instead of letting the quadratic
interpolate noise.

  $ cat > saturated-quadratic.csv <<'EOF'
  > n,time
  > 1,10
  > 2,11
  > 3,10
  > EOF
  $ guesstimator fit --normalize-samples=false saturated-quadratic.csv | grep -E '^(Observations|Best by BIC):|^  polynomial'
  Observations: 3
  Best by BIC: constant

A near-perfect linear instruction-count trace should not select a high-degree
polynomial or quasi-polynomial just because it can shave tiny residuals off the
linear fit. The model-selection noise floor makes these near-zero residuals
equivalent and lets the BIC parameter penalty prefer the linear model.

  $ cat > near-perfect-linear-instructions.csv <<'EOF'
  > n,time
  > 256,1451942
  > 384,2171558
  > 512,2891174
  > 768,4330406
  > 1024,5769638
  > 1536,8648102
  > 2048,11526566
  > 3072,17283494
  > 4096,23040423
  > 6144,34554279
  > 8192,46068137
  > EOF
  $ guesstimator fit near-perfect-linear-instructions.csv | awk -F': ' '/Best by BIC/ {print $2}'
  polynomial-1
  $ guesstimator assert --max-delta-bic=0 polynomial-1 near-perfect-linear-instructions.csv

A large-scale finite quadratic should not lose to a much worse lower-parameter
power law just because a broad variance floor hides the residual difference.

  $ python3 - <<'PY'
  > with open('large-quadratic.csv', 'w') as out:
  >     out.write('n,time\n')
  >     for n in range(1_000_000, 12_000_000, 1_000_000):
  >         t = 1.0 + 2.0 * n + 0.5 * n * n
  >         out.write(f'{n},{t:.17g}\n')
  > PY
  $ guesstimator fit --normalize-samples=false large-quadratic.csv | grep 'Best by BIC'
  Best by BIC: polynomial-2

Repeated problem sizes should not force the polynomial search into an
unidentifiable higher degree and abort the whole estimate.

  $ cat > repeated-sizes.csv <<'EOF'
  > n,time
  > 1,3.0
  > 1,3.1
  > 2,5.0
  > 2,5.1
  > EOF
  $ guesstimator fit --normalize-samples=false repeated-sizes.csv | awk '/^Observations:/ {print}; /^Best by BIC:/ {print "Best by BIC: reported"}'
  Observations: 4
  Best by BIC: reported

Finite but enormous timings should not make residual or summary-statistic
sums-of-squares overflow abort the entire estimate.

  $ cat > huge-times.csv <<'EOF'
  > n,time
  > 1,1e200
  > 2,2e200
  > 3,3e200
  > 4,4e200
  > EOF
  $ guesstimator fit --normalize-samples=false huge-times.csv | awk '/^Observations:/ {print}; /^Best by BIC:/ {print "Best by BIC: reported"}'
  Observations: 4
  Best by BIC: reported
