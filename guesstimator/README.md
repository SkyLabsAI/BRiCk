# guesstimator

Guesstimator is a library for regression analysis, i.e. it tries to
establish a relation between an input variable, which we call "problem
size", and an observed outcome, which we call "time", by trying to fit
samples to a hardcoded list of candidate function shapes.

Guesstimator currently supports the following function shapes:
- constant functions ([f x = c])
- logarithmic functions ([f x = c * log x])
- polynomial functions ([f x = c_n * x^n + .. + c_0 * x^0 ])
- quasi-polynomial functions
  ([f x = log x * c_n * x^n + c_(n-1) * x^(n-1) + .. c_0 * x^0])
- exponential functions ([f x = c * e^x])
- power laws

Guesstimator uses several statistical tools to evaluate which function shape
is the most likely best fit for the given samples.

1. Within polynomial and quasi-polynomial families, nested
extra-sum-of-squares F tests measure whether an added term is statistically
detectable. By default, the richer model must also exceed an explicit
model-selection resolution so sub-ppm residual structure does not determine the
dominant growth class.

2. Between retained family representatives, Guesstimator uses the Bayesian information criterion
(BIC) (and The Akaike information criterion (AIC) for tie breaking) to rank
candidate functions.

Guesstimator supports two modes of interaction:
- `fit`: fit the data onto all candidate functions and return information
  about the fits
- `assert`: assert that the data fits a given function shape and that it is
  the best fit out of all the known function shapes. Succeeds only if these
  conditions are met and fails otherwise.

** Holdouts

Guesstimator supports options to repeat the estimation with held out values in order
to determine the stability of the estimation. Grouped k-fold holdouts can be
used to guard against sensitivity to individual measurements. Tail holdout
options can be used to check if the candidate model selection is sensitive
to the tail of the data samples sorted by problem size.

# Usage

Use `guesstimator fit <file.csv>` on a csv file with `problem_size,time` format to
get an overview of how well the available function shapes fit the data. Example
output on tests/inputs/polynomial.csv:

```
$ guesstimator fit test/inputs/polynomial.csv
Input: test/inputs/polynomial.csv
Header: yes
Normalized samples: yes
Fit parameter scale: original problem size
Model-selection resolution: 1e-06
Observations: 7
Best by BIC: polynomial-2
Fits:
  polynomial-2  RSS= 4.307e-25  R^2= 1.0000  AIC= -154.228  BIC= -154.390  intercept=1, linear=0.5, quadratic=0.25
  power-law     RSS=     21.21  R^2= 1.0000  AIC=   11.760  BIC=   11.652  coefficient=0.32509, log_coefficient=-1.1237, exponent=1.9444
  exponential   RSS= 1.135e+04  R^2= 0.9874  AIC=   55.736  BIC=   55.628  coefficient=37.384, log_coefficient=3.6212, rate=0.05231
  logarithmic   RSS= 3.951e+05  R^2= 0.5626  AIC=   80.586  BIC=   80.478  intercept=-199.01, log_coefficient=194.34
  constant      RSS= 9.031e+05  R^2= 0.0000  AIC=   84.374  BIC=   84.320  constant=205.11
```


Use `guesstimator assert <class> <file.csv>` to test if `<class>` is the best
fit (and also, absolutely, a good fit) for <file.csv>.

```
$ guesstimator assert logarithmic test/inputs/polynomial.csv # fails
$ guesstimator assert polynomial-2 test/inputs/polynomial.csv # succeeds
```


`guesstimator fit --help` and `guesstimator assert --help` have explanations of
the various options that are available.


## LLM-Generated README.md:

An OCaml/dune project that estimates algorithmic complexity from runtime observations `(problem_size, time)`.

The library fits these candidate models:

- constant: `t = a`
- logarithmic: `t = a + b log n`
- polynomial: `t = a0 + a1 n + ... + ad n^d` via ordinary least squares.
  The estimator searches increasing degrees and stops when an extra-sum-of-squares
  F test says the next degree is not significant over the previous one. Selected
  polynomial degrees are displayed as `polynomial-d`.
- quasi-polynomial: `t = a0 + a1 n + ... + ad n^d log n`, where only the
  highest-degree term is multiplied by `log n`. Selected quasi-polynomial degrees
  are displayed as `quasi-polynomial-d`.
- power law: `t = c n^p` via one-dimensional nonlinear least squares on the
  original time scale
- exponential: `t = c exp(k n)` via one-dimensional nonlinear least squares on
  the original time scale

Models are ranked by BIC/AIC and residual error on the original time scale.
Pairwise comparisons use an extra-sum-of-squares F test only for nested
restricted-versus-richer comparisons; non-nested models are selected by BIC.
For a one-parameter polynomial or quasi-polynomial promotion, statistical
significance and practical materiality are reported separately, and only a
materially supported addition advances.
Comparison output is optional: `--print-comparisons=across` prints comparisons
across distinct complexity classes, `within` prints comparisons within a class
(for example, polynomial degree choices), and `all` prints both under separate
headings. `--print-loser-fits` independently prints full fit statistics for
models that lost an exposed or selection-internal comparison and are not already
listed under `Fits`; models that were fitted but never compared are omitted.
`polynomial-X` and `polynomial-Y` are treated as the same class with different
degrees, as are `quasi-polynomial-X` and `quasi-polynomial-Y`. When same-degree
polynomial and quasi-polynomial fits are very close, their
comparison is resolved by a ratio-stability diagnostic for the leading term.
Power-law and exponential fits report both `coefficient` when representable and
`log_coefficient`, which is also used internally for stable prediction.

### Build and run

Local build
```sh
dune b
dune exec -- guestimator
```

Note: Use `dune exec -- guesstimator` when running examples with having
installed the tool.

Examples:
```sh
guesstimator fit timings.csv
# disable default problem-size normalization
guesstimator fit --normalize-samples=false timings.csv
# inspect legacy zero-resolution nested selection
guesstimator fit --model-selection-resolution=0 timings.csv
# inspect parameters in the normalized fitted coordinate
guesstimator fit --fit-parameter-scale=normalized timings.csv
# include comparisons and their rationale notes
guesstimator fit --print-comparisons=all --verbose timings.csv
# show statistics for compared candidates that lost and are not in Fits
guesstimator fit --print-loser-fits timings.csv
# check that the best fit is polynomial-2; exits 0 on match, 1 on mismatch
guesstimator assert polynomial-2 timings.csv
```

The `guesstimator fit` subcommand reads a CSV file with two columns: problem size and
time. By default, the command normalizes problem sizes by dividing by the largest
problem size in the input, yielding values in `(0, 1]`, for numerically stable
fitting; pass `--normalize-samples=false` to fit raw problem sizes instead.
Printed fit parameters are converted back to the original input problem-size
units by default. Pass `--fit-parameter-scale=normalized` to print the fitted
normalized coordinate instead. When converted to original units,
quasi-polynomial parameters may include an extra non-log highest-degree
polynomial term induced by the change of variables. If the best fit has relative
RSME above 20%, `fit` appends a warning to the `Best by BIC` line. Use
`--holdout` to run grouped round-robin holdout validation by problem size, and
`--holdout-tail` to train on smaller problem sizes and test on the largest ones.
These report the selected classes together with median/max held-out relative
RSME. Defaults are 5 folds, a 25% tail holdout, and an 80% stability threshold;
use `--holdout-folds`, `--holdout-tail-fraction`, and
`--holdout-stability-threshold` to adjust them. Holdout tuning options must be
paired with the mode they configure: `--holdout-folds` requires `--holdout`,
`--holdout-tail-fraction` requires `--holdout-tail`, and
`--holdout-stability-threshold` requires at least one holdout mode. Invalid
combinations print an error and exit with status 102.

`guesstimator assert CLASS FILE` performs the same fit, including default
problem-size normalization and model-selection resolution, without printing
output. A requested polynomial or quasi-polynomial degree may be fitted for
comparison, but it cannot bypass the same materiality rule or redefine the
normal selected best. The command exits with status 0 if `CLASS` is materially
eligible and is the best retained fit or within `--max-delta-bic` of it (default
2.0), status 1 if it is not, status 100 if the normal best fit is suspicious by
the same relative RSME rule, or status 101 if requested holdout validation does not reach
the stability threshold. Pass `--max-delta-bic=0` for strict best-fit matching,
and pass `--normalize-samples=false` to assert against raw problem sizes.
`CLASS` uses the canonical names printed by `fit`: `constant`, `logarithmic`,
`polynomial-N`, `quasi-polynomial-N`, `power-law`, or `exponential`. Files may
include a header row, which is auto-detected unless
`--header=true` or `--header=false` is supplied. Problem sizes and times must be
finite positive numbers. The estimator needs residual degrees of freedom for
every fitted model, so it tries polynomial degrees only up to `observations - 2`
and the number of distinct problem sizes minus one, and requires at least three
observations overall.

### Model-selection resolution

The default model-selection resolution is `1e-6`. It is a smallest effect size
of interest (SESOI) for identifying the dominant observed growth shape, not an
estimate of benchmark noise. For a simpler and richer nested least-squares model
that differ by one parameter, Guesstimator computes

```text
improvement = RSS_simple - RSS_rich
scale = sum((time - mean_time)^2)
relative_effect = sqrt(improvement / scale)
relative_standard_error = sqrt((RSS_rich / residual_df) / scale)
```

It forms a two-sided model-based `(1 - alpha)` interval around the relative
effect. The outcome is:

- `material` if the full interval is above the resolution;
- `equivalent` if the full interval is below it;
- `inconclusive` if the interval overlaps it.

Only a material effect promotes polynomial degree or admits a quasi-polynomial
term over its natural polynomial reference. Equivalent and inconclusive results
select the simpler model; choosing simplicity for an inconclusive result is an
explicit conservative policy, not proof that the richer term is zero. Detailed
comparison output shows the p-value, effect interval, resolution, and outcome.
The ordinary `significant=yes|no` field retains its p-value meaning.

The interval assumes a fixed design with independent, homoscedastic Gaussian
residuals and uses observed response variation as its reporting scale.
Heteroscedasticity, correlated measurements, deterministic counters, and the
sequential degree search limit confirmatory coverage, so the interval is a
selection diagnostic rather than post-selection inference. Repeated timings at
the same problem size are preferable when measurement variability needs to be
estimated directly.

Set `--model-selection-resolution=0` to recover legacy one-parameter F-test
promotion. The configured value is used consistently by `fit`, `assert`, and all
holdout reruns. Positive scaling of all times does not change the materiality
decision, and additive offsets do not change it for models with an intercept.
The resolution is based on the sampled range: weak curvature that is globally
small but important only at the largest sizes can still be simplified. Users
making consequential classifications should inspect sensitivity at several
resolutions and report the chosen value.

Raw RSS, R², AIC, and BIC are not clamped or rewritten by this policy. BIC ranks
the family representatives retained by within-family materiality selection; it
does not rank every degree that was fitted for diagnostics.

### Notes

The polynomial analysis is numerically more reliable when problem sizes are in a
moderate range. The CLI therefore normalizes problem sizes to `(0, 1]` by default.
Library callers can opt into the same preprocessing with
`Guesstimator.normalize_samples`; `fit` and `estimate` themselves use the samples
they are given and do not normalize implicitly. If you normalize inputs yourself,
keep them away from zero, for example in `(0, 1]` or `[epsilon, 1]`, because
logarithmic, power-law, and quasi-polynomial models require positive problem
sizes.

The result is statistical evidence about the observed finite data, not a proof
of asymptotic complexity. Timing noise is often heteroscedastic and affected by
warmup, cache behavior, garbage collection, CPU frequency changes, and scheduler
interference. Power-law and polynomial families also overlap on finite samples
(for example, `n^2` is both a monomial and a power law).

Running the full test suite requires common Unix tools used by cram tests,
including `python3` and `awk`.
