#!/usr/bin/env python3
"""Generate SVG plots for the statistical bug report.

The script intentionally uses only the Python standard library so the plots can
be regenerated in a minimal OCaml/dune development environment.
"""

from __future__ import annotations

import html
import math
from pathlib import Path
from typing import Callable, Iterable, NamedTuple

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "docs" / "statistical-bugs"

COLORS = {
    "data": "#111827",
    "blue": "#2563eb",
    "red": "#dc2626",
    "green": "#16a34a",
    "orange": "#ea580c",
    "purple": "#7c3aed",
    "gray": "#6b7280",
}


class Fit(NamedTuple):
    label: str
    parameters: tuple[float, ...]
    rss: float
    bic: float
    predict: Callable[[float], float]


def solve_linear_system(matrix: list[list[float]], rhs: list[float]) -> list[float]:
    n = len(rhs)
    a = [row[:] for row in matrix]
    b = rhs[:]
    for k in range(n):
        pivot = max(range(k, n), key=lambda i: abs(a[i][k]))
        if abs(a[pivot][k]) < 1e-15:
            raise ValueError("singular matrix")
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            b[k], b[pivot] = b[pivot], b[k]
        for i in range(k + 1, n):
            factor = a[i][k] / a[k][k]
            a[i][k] = 0.0
            for j in range(k + 1, n):
                a[i][j] -= factor * a[k][j]
            b[i] -= factor * b[k]
    x = [0.0] * n
    for i in range(n - 1, -1, -1):
        total = b[i] - sum(a[i][j] * x[j] for j in range(i + 1, n))
        x[i] = total / a[i][i]
    return x


def linear_regression(rows: list[list[float]], ys: list[float]) -> list[float]:
    p = len(rows[0])
    xtx = [[0.0] * p for _ in range(p)]
    xty = [0.0] * p
    for row, y in zip(rows, ys):
        for j in range(p):
            xty[j] += row[j] * y
            for k in range(p):
                xtx[j][k] += row[j] * row[k]
    return solve_linear_system(xtx, xty)


def rss(ys: Iterable[float], predictions: Iterable[float]) -> float:
    return sum((y - p) ** 2 for y, p in zip(ys, predictions))


def bic(value: float, n: int, k: int) -> float:
    return n * math.log(max(1e-12, value / n)) + k * math.log(n)


def fit_polynomial(xs: list[float], ys: list[float]) -> Fit:
    a, b, c = linear_regression([[1.0, x, x * x] for x in xs], ys)

    def predict(x: float) -> float:
        return a + b * x + c * x * x

    value = rss(ys, [predict(x) for x in xs])
    return Fit("polynomial", (a, b, c), value, bic(value, len(xs), 3), predict)


def fit_constant(xs: list[float], ys: list[float]) -> Fit:
    (a,) = linear_regression([[1.0] for _ in xs], ys)

    def predict(_x: float) -> float:
        return a

    value = rss(ys, [predict(x) for x in xs])
    return Fit("constant", (a,), value, bic(value, len(xs), 1), predict)


def fit_power_time_scale(xs: list[float], ys: list[float]) -> Fit:
    logs = [math.log(x) for x in xs]

    def rss_for(p: float) -> tuple[float, float]:
        zs = [math.exp(p * log_x) for log_x in logs]
        coefficient = sum(y * z for y, z in zip(ys, zs)) / sum(z * z for z in zs)
        value = rss(ys, [coefficient * z for z in zs])
        return value, coefficient

    a, b = -5.0, 5.0
    gr = (math.sqrt(5.0) - 1.0) / 2.0
    c = b - gr * (b - a)
    d = a + gr * (b - a)
    fc, _ = rss_for(c)
    fd, _ = rss_for(d)
    for _ in range(160):
        if fc > fd:
            a, c, fc = c, d, fd
            d = a + gr * (b - a)
            fd, _ = rss_for(d)
        else:
            b, d, fd = d, c, fc
            c = b - gr * (b - a)
            fc, _ = rss_for(c)
    exponent = (a + b) / 2.0
    value, coefficient = rss_for(exponent)

    def predict(x: float) -> float:
        return coefficient * (x**exponent)

    return Fit("time-scale power-law", (coefficient, exponent), value, bic(value, len(xs), 2), predict)


def fit_exponential_log_space(xs: list[float], ys: list[float]) -> Fit:
    a, k = linear_regression([[1.0, x] for x in xs], [math.log(y) for y in ys])
    coefficient = math.exp(a)

    def predict(x: float) -> float:
        return coefficient * math.exp(k * x)

    value = rss(ys, [predict(x) for x in xs])
    return Fit("log-regression exponential", (coefficient, k), value, bic(value, len(xs), 2), predict)


def fit_exponential_at_rate(xs: list[float], ys: list[float], rate: float, label: str) -> Fit:
    zs = [math.exp(rate * x) for x in xs]
    coefficient = sum(y * z for y, z in zip(ys, zs)) / sum(z * z for z in zs)

    def predict(x: float) -> float:
        return coefficient * math.exp(rate * x)

    value = rss(ys, [predict(x) for x in xs])
    return Fit(label, (coefficient, rate), value, bic(value, len(xs), 2), predict)


def fit_exponential_time_scale(xs: list[float], ys: list[float]) -> Fit:
    def rss_for(k: float) -> tuple[float, float]:
        zs = [math.exp(k * x) for x in xs]
        coefficient = sum(y * z for y, z in zip(ys, zs)) / sum(z * z for z in zs)
        value = rss(ys, [coefficient * z for z in zs])
        return value, coefficient

    # One-dimensional nonlinear least-squares search over the rate.  The data
    # used here are small and positive; this bracket covers the synthetic case.
    a, b = -1.0, 2.0
    gr = (math.sqrt(5.0) - 1.0) / 2.0
    c = b - gr * (b - a)
    d = a + gr * (b - a)
    fc, _ = rss_for(c)
    fd, _ = rss_for(d)
    for _ in range(160):
        if fc > fd:
            a, c, fc = c, d, fd
            d = a + gr * (b - a)
            fd, _ = rss_for(d)
        else:
            b, d, fd = d, c, fc
            c = b - gr * (b - a)
            fc, _ = rss_for(c)
    rate = (a + b) / 2.0
    value, coefficient = rss_for(rate)

    def predict(x: float) -> float:
        return coefficient * math.exp(rate * x)

    return Fit("time-scale exponential", (coefficient, rate), value, bic(value, len(xs), 2), predict)


def dense_points(xmin: float, xmax: float, count: int = 240) -> list[float]:
    if count <= 1:
        return [xmin]
    return [xmin + (xmax - xmin) * i / (count - 1) for i in range(count)]


def fmt(value: float) -> str:
    if abs(value) >= 1000 or (value != 0 and abs(value) < 0.001):
        return f"{value:.3g}"
    return f"{value:.4g}"


def nice_ticks(lo: float, hi: float, count: int = 5) -> list[float]:
    if lo == hi:
        return [lo]
    return [lo + (hi - lo) * i / (count - 1) for i in range(count)]


def write_plot(
    path: Path,
    title: str,
    subtitle: str,
    xs: list[float],
    ys: list[float],
    series: list[dict],
    extra_points: list[dict] | None = None,
) -> None:
    extra_points = extra_points or []
    width, height = 900, 560
    left, right, top, bottom = 78, 34, 72, 78
    plot_w = width - left - right
    plot_h = height - top - bottom

    all_x = xs[:]
    all_y = ys[:]
    for s in series:
        for x, y in s["points"]:
            all_x.append(x)
            all_y.append(y)
    for p in extra_points:
        all_x.append(p["x"])
        all_y.append(p["y"])

    xmin, xmax = min(all_x), max(all_x)
    ymin, ymax = min(all_y), max(all_y)
    xpad = (xmax - xmin) * 0.04 or 1.0
    ypad = (ymax - ymin) * 0.10 or 1.0
    xmin -= xpad
    xmax += xpad
    ymin -= ypad
    ymax += ypad

    def sx(x: float) -> float:
        return left + (x - xmin) / (xmax - xmin) * plot_w

    def sy(y: float) -> float:
        return top + (ymax - y) / (ymax - ymin) * plot_h

    lines: list[str] = []
    lines.append(f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">')
    lines.append("<style>text{font-family:Inter,Arial,sans-serif;fill:#111827}.title{font-size:22px;font-weight:700}.subtitle{font-size:14px;fill:#374151}.tick{font-size:12px;fill:#4b5563}.legend{font-size:13px}.axis{stroke:#111827;stroke-width:1.2}.grid{stroke:#e5e7eb;stroke-width:1}.curve{fill:none;stroke-width:2.8}.point{stroke:#fff;stroke-width:1.2}</style>")
    lines.append(f'<rect x="0" y="0" width="{width}" height="{height}" fill="#ffffff"/>')
    lines.append(f'<text class="title" x="{left}" y="32">{html.escape(title)}</text>')
    lines.append(f'<text class="subtitle" x="{left}" y="55">{html.escape(subtitle)}</text>')

    for t in nice_ticks(xmin, xmax):
        x = sx(t)
        lines.append(f'<line class="grid" x1="{x:.2f}" y1="{top}" x2="{x:.2f}" y2="{top + plot_h}"/>')
        lines.append(f'<text class="tick" x="{x:.2f}" y="{top + plot_h + 22}" text-anchor="middle">{html.escape(fmt(t))}</text>')
    for t in nice_ticks(ymin, ymax):
        y = sy(t)
        lines.append(f'<line class="grid" x1="{left}" y1="{y:.2f}" x2="{left + plot_w}" y2="{y:.2f}"/>')
        lines.append(f'<text class="tick" x="{left - 10}" y="{y + 4:.2f}" text-anchor="end">{html.escape(fmt(t))}</text>')

    lines.append(f'<line class="axis" x1="{left}" y1="{top + plot_h}" x2="{left + plot_w}" y2="{top + plot_h}"/>')
    lines.append(f'<line class="axis" x1="{left}" y1="{top}" x2="{left}" y2="{top + plot_h}"/>')
    lines.append(f'<text class="tick" x="{left + plot_w / 2}" y="{height - 28}" text-anchor="middle">problem size n</text>')
    lines.append(f'<text class="tick" transform="translate(22 {top + plot_h / 2}) rotate(-90)" text-anchor="middle">time</text>')

    for s in series:
        points = " ".join(f'{sx(x):.2f},{sy(y):.2f}' for x, y in s["points"])
        dash = f' stroke-dasharray="{s["dash"]}"' if s.get("dash") else ""
        lines.append(f'<polyline class="curve" points="{points}" stroke="{s["color"]}"{dash}/>' )

    for x, y in zip(xs, ys):
        lines.append(f'<circle class="point" cx="{sx(x):.2f}" cy="{sy(y):.2f}" r="4.5" fill="{COLORS["data"]}"/>')

    for p in extra_points:
        fill = p.get("color", COLORS["orange"])
        lines.append(f'<circle cx="{sx(p["x"]):.2f}" cy="{sy(p["y"]):.2f}" r="5.5" fill="{fill}" stroke="#fff" stroke-width="1.4"/>')
        lines.append(f'<text class="legend" x="{sx(p["x"]) + 8:.2f}" y="{sy(p["y"]) - 8:.2f}">{html.escape(p["label"])}</text>')

    legend_x = left + plot_w - 330
    legend_y = top + 18
    lines.append(f'<rect x="{legend_x - 14}" y="{legend_y - 20}" width="344" height="{24 * (len(series) + 1)}" rx="8" fill="#ffffff" stroke="#e5e7eb"/>')
    lines.append(f'<circle cx="{legend_x}" cy="{legend_y}" r="4.5" fill="{COLORS["data"]}"/>')
    lines.append(f'<text class="legend" x="{legend_x + 16}" y="{legend_y + 4}">observations</text>')
    for i, s in enumerate(series, start=1):
        y = legend_y + 24 * i
        dash = f' stroke-dasharray="{s["dash"]}"' if s.get("dash") else ""
        lines.append(f'<line x1="{legend_x - 6}" y1="{y}" x2="{legend_x + 10}" y2="{y}" stroke="{s["color"]}" stroke-width="2.8"{dash}/>' )
        lines.append(f'<text class="legend" x="{legend_x + 16}" y="{y + 4}">{html.escape(s["label"])}</text>')

    lines.append("</svg>")
    path.write_text("\n".join(lines) + "\n")


def plot_log_space_ranking() -> None:
    xs = [1, 2, 3, 4, 5]
    ys = [2.04872127, 2.31828183, 4.88168907, 6.98905610, 12.58249396]
    poly = fit_polynomial(xs, ys)
    exp_log = fit_exponential_log_space(xs, ys)
    exp_time = fit_exponential_time_scale(xs, ys)
    grid = dense_points(min(xs), max(xs))
    write_plot(
        OUT / "log_space_vs_time_scale_exponential.svg",
        "Fixed: exponential fit is optimized on the ranking scale",
        "Before the fix, log-space parameters made polynomial look better than a time-scale exponential fit.",
        xs,
        ys,
        [
            {"label": f"pre-fix selected polynomial RSS={poly.rss:.4f}", "color": COLORS["red"], "points": [(x, poly.predict(x)) for x in grid]},
            {"label": f"pre-fix log-reg exp RSS={exp_log.rss:.4f}", "color": COLORS["gray"], "dash": "7 5", "points": [(x, exp_log.predict(x)) for x in grid]},
            {"label": f"fixed time-scale exp RSS={exp_time.rss:.4f}", "color": COLORS["blue"], "points": [(x, exp_time.predict(x)) for x in grid]},
        ],
    )


def plot_non_nested_f_test() -> None:
    xs = [float(n) for n in range(1, 61)]
    ys = [
        100 + 4.9378446115 * (((n - 30.5) / 60) ** 2 - 3599 / 43200) + 1.0542168675 * math.sin(0.2 * n)
        for n in xs
    ]
    poly = fit_polynomial(xs, ys)
    power = fit_power_time_scale(xs, ys)
    grid = dense_points(min(xs), max(xs))
    write_plot(
        OUT / "non_nested_f_test.svg",
        "Fixed: non-nested comparisons do not run F-tests",
        "Before the fix, an invalid F-test picked polynomial; BIC correctly keeps power-law.",
        xs,
        ys,
        [
            {"label": f"pre-fix F-test winner polynomial BIC={poly.bic:.3f}", "color": COLORS["red"], "points": [(x, poly.predict(x)) for x in grid]},
            {"label": f"fixed BIC winner power-law BIC={power.bic:.3f}", "color": COLORS["blue"], "dash": "7 5", "points": [(x, power.predict(x)) for x in grid]},
        ],
    )


def plot_exact_richer_nan() -> None:
    xs = [1, 2, 3, 4]
    ys = [2, 5, 10, 17]
    const = fit_constant(xs, ys)
    poly = fit_polynomial(xs, ys)
    grid = dense_points(min(xs), max(xs))
    write_plot(
        OUT / "exact_richer_nan.svg",
        "Fixed: exact richer fits have p=0, not NaN",
        "Before the fix, constant vs polynomial reported constant despite zero polynomial residual error.",
        xs,
        ys,
        [
            {"label": f"pre-fix pairwise winner constant RSS={const.rss:.0f}", "color": COLORS["red"], "points": [(x, const.predict(x)) for x in grid]},
            {"label": f"fixed exact polynomial RSS={poly.rss:.0g}", "color": COLORS["blue"], "points": [(x, poly.predict(x)) for x in grid]},
        ],
    )


def plot_nonlinear_search() -> None:
    xs = [1, 2, 3, 4]
    ys = [40.35105755137664, 0.2693556159897494, 8.758890089379172, 29.94111029566006]
    old = fit_exponential_at_rate(xs, ys, -4.390456277601887, "pre-fix local-bracket exponential")
    fixed = fit_exponential_time_scale(xs, ys)
    grid = dense_points(min(xs), max(xs))
    write_plot(
        OUT / "nonlinear_search.svg",
        "Fixed: nonlinear slope search uses broad grid refinement",
        "Before the fix, one-sided bracketing missed a lower-RSS exponential slope.",
        xs,
        ys,
        [
            {"label": f"pre-fix local slope RSS={old.rss:.1f}", "color": COLORS["red"], "points": [(x, old.predict(x)) for x in grid]},
            {"label": f"fixed refined slope RSS={fixed.rss:.1f}", "color": COLORS["blue"], "dash": "7 5", "points": [(x, fixed.predict(x)) for x in grid]},
        ],
    )


def plot_saturated_quadratic() -> None:
    xs = [1, 2, 3]
    ys = [10, 11, 10]
    const = fit_constant(xs, ys)
    poly = fit_polynomial(xs, ys)
    grid = dense_points(1, 4)
    write_plot(
        OUT / "saturated_quadratic.svg",
        "Fixed: saturated quadratic fits are rejected",
        "Before the fix, a three-point quadratic interpolated noise and missed a plausible held-out point.",
        xs,
        ys,
        [
            {"label": f"pre-fix saturated quadratic RSS={poly.rss:.1g}", "color": COLORS["red"], "points": [(x, poly.predict(x)) for x in grid]},
            {"label": f"constant alternative RSS={const.rss:.4f}", "color": COLORS["blue"], "dash": "7 5", "points": [(x, const.predict(x)) for x in grid]},
        ],
        extra_points=[{"x": 4, "y": 10, "label": "held-out n=4,t=10", "color": COLORS["orange"]}],
    )


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    plot_log_space_ranking()
    plot_non_nested_f_test()
    plot_exact_richer_nan()
    plot_nonlinear_search()
    plot_saturated_quadratic()
    print(f"wrote plots to {OUT}")


if __name__ == "__main__":
    main()
