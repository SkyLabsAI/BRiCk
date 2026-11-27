#!/usr/bin/env python3
"""Offline sensitivity study for Guesstimator's model-selection resolution.

This is not part of the test suite and does not establish universal coverage.
It exercises the material/equivalent/inconclusive policy under a fixed-design
linear-versus-quadratic simulation using only the Python standard library.
"""

from __future__ import annotations

import argparse
import math
import random
import statistics
from collections import Counter


def solve(matrix: list[list[float]], rhs: list[float]) -> list[float]:
    """Solve a small dense system with partial pivoting."""
    n = len(rhs)
    augmented = [row[:] + [value] for row, value in zip(matrix, rhs)]
    for column in range(n):
        pivot = max(range(column, n), key=lambda row: abs(augmented[row][column]))
        if abs(augmented[pivot][column]) < 1e-15:
            raise ValueError("singular simulation design")
        augmented[column], augmented[pivot] = augmented[pivot], augmented[column]
        divisor = augmented[column][column]
        for index in range(column, n + 1):
            augmented[column][index] /= divisor
        for row in range(n):
            if row == column:
                continue
            factor = augmented[row][column]
            for index in range(column, n + 1):
                augmented[row][index] -= factor * augmented[column][index]
    return [augmented[row][n] for row in range(n)]


def polynomial_rss(xs: list[float], ys: list[float], degree: int) -> float:
    columns = degree + 1
    matrix = [[0.0 for _ in range(columns)] for _ in range(columns)]
    rhs = [0.0 for _ in range(columns)]
    for x, y in zip(xs, ys):
        powers = [1.0]
        for _ in range(degree):
            powers.append(powers[-1] * x)
        for left in range(columns):
            rhs[left] += powers[left] * y
            for right in range(columns):
                matrix[left][right] += powers[left] * powers[right]
    coefficients = solve(matrix, rhs)
    return sum(
        (y - sum(coefficient * (x**power) for power, coefficient in enumerate(coefficients))) ** 2
        for x, y in zip(xs, ys)
    )


def t_critical_975(df: int) -> float:
    """Accurate large-df Cornish-Fisher approximation for this offline study."""
    z = statistics.NormalDist().inv_cdf(0.975)
    inverse = 1.0 / df
    return (
        z
        + (z**3 + z) * inverse / 4.0
        + (5.0 * z**5 + 16.0 * z**3 + 3.0 * z) * inverse**2 / 96.0
        + (3.0 * z**7 + 19.0 * z**5 + 17.0 * z**3 - 15.0 * z)
        * inverse**3
        / 384.0
    )


def classify(xs: list[float], ys: list[float], resolution: float) -> str:
    rss_linear = polynomial_rss(xs, ys, 1)
    rss_quadratic = polynomial_rss(xs, ys, 2)
    mean = sum(ys) / len(ys)
    tss = sum((value - mean) ** 2 for value in ys)
    improvement = max(0.0, rss_linear - rss_quadratic)
    effect = math.sqrt(improvement / tss)
    df = len(ys) - 3
    standard_error = math.sqrt((rss_quadratic / df) / tss)
    margin = t_critical_975(df) * standard_error
    lower = max(0.0, effect - margin)
    upper = effect + margin
    if lower > resolution:
        return "material"
    if upper < resolution:
        return "equivalent"
    return "inconclusive"


def standardized_design(count: int, true_effect: float) -> tuple[list[float], list[float], float]:
    xs = [-1.0 + 2.0 * index / (count - 1) for index in range(count)]
    quadratic = [x * x for x in xs]
    quadratic_mean = sum(quadratic) / count
    residualized_quadratic = [value - quadratic_mean for value in quadratic]
    baseline = [100.0 + 50.0 * x for x in xs]
    baseline_mean = sum(baseline) / count
    baseline_ss = sum((value - baseline_mean) ** 2 for value in baseline)
    quadratic_ss = sum(value * value for value in residualized_quadratic)
    target_added_ss = true_effect**2 * baseline_ss / max(1e-300, 1.0 - true_effect**2)
    coefficient = math.sqrt(target_added_ss / quadratic_ss)
    truth = [
        base + coefficient * quadratic_value
        for base, quadratic_value in zip(baseline, residualized_quadratic)
    ]
    response_sd = math.sqrt(baseline_ss / count)
    return xs, truth, response_sd


def noise(rng: random.Random, xs: list[float], sigma: float, scenario: str) -> list[float]:
    if scenario == "iid":
        return [rng.gauss(0.0, sigma) for _ in xs]
    if scenario == "heteroskedastic":
        return [rng.gauss(0.0, sigma * (0.5 + abs(x))) for x in xs]
    if scenario == "ar1":
        values: list[float] = []
        previous = rng.gauss(0.0, sigma)
        innovation_sigma = sigma * math.sqrt(1.0 - 0.8**2)
        for _ in xs:
            previous = 0.8 * previous + rng.gauss(0.0, innovation_sigma)
            values.append(previous)
        return values
    raise ValueError(scenario)


def run(trials: int, seed: int, resolution: float) -> None:
    rng = random.Random(seed)
    print(
        f"trials={trials} seed={seed} resolution={resolution:g} "
        "n=100 noise_sd=1e-6*response_sd"
    )
    for scenario in ("iid", "heteroskedastic", "ar1"):
        for true_effect in (0.5e-6, 1.0e-6, 2.0e-6):
            xs, truth, response_sd = standardized_design(100, true_effect)
            counts: Counter[str] = Counter()
            for _ in range(trials):
                errors = noise(rng, xs, response_sd * 1e-6, scenario)
                ys = [expected + error for expected, error in zip(truth, errors)]
                counts[classify(xs, ys, resolution)] += 1
            print(
                f"{scenario:16s} true_effect={true_effect:.1e} "
                f"material={counts['material']/trials:.3f} "
                f"equivalent={counts['equivalent']/trials:.3f} "
                f"inconclusive={counts['inconclusive']/trials:.3f}"
            )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--trials", type=int, default=1000)
    parser.add_argument("--seed", type=int, default=20260722)
    parser.add_argument("--resolution", type=float, default=1e-6)
    args = parser.parse_args()
    if args.trials <= 0:
        parser.error("--trials must be positive")
    run(args.trials, args.seed, args.resolution)


if __name__ == "__main__":
    main()
