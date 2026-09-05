#!/usr/bin/env python3
"""
SL-1.B extended probe (Case-iiib) for near-complete one-divisible templates.

Checks (composite n in [n_min, n_max]):
1) Case-iiib selection (Case-B + 1,n-1 in E_fix + U_fix(0)=Z_n)
2) Best residue r* maximizing miss measure m(r)
3) Bound check: m(r*) >= 1/(e_max*(e_max-1))
4) Endpoint denominator check: den <= n
5) Integer b-witness at M=1 (L=L0) on at least one miss interval

Outputs:
- per-template CSV
- summary text
"""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from fractions import Fraction
from functools import reduce
from itertools import combinations
from math import gcd, lcm
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple


def ext_gcd(a: int, b: int) -> Tuple[int, int, int]:
    if a == 0:
        return b, 0, 1
    g, x, y = ext_gcd(b % a, a)
    return g, y - (b // a) * x, x


def modinv(a: int, n: int) -> int | None:
    g, x, _ = ext_gcd(a % n, n)
    if g != 1:
        return None
    return x % n


def bad_set(e: int, t: int, n: int) -> set[int]:
    g = gcd(e, n)
    n1 = n // g
    e1 = e // g
    inv = modinv(e1, n1)
    if inv is None:
        return set()

    out: set[int] = set()
    for rr in ((-t) % n, (-(t + 1)) % n):
        if rr % g != 0:
            continue
        a0 = ((rr // g) * inv) % n1
        for k in range(g):
            out.add((a0 + k * n1) % n)
    return out


def merge_intervals(intervals: Sequence[Tuple[Fraction, Fraction]]) -> List[Tuple[Fraction, Fraction]]:
    items = sorted((a, b) for a, b in intervals if a < b)
    merged: List[List[Fraction]] = []
    for a, b in items:
        if not merged or a > merged[-1][1]:
            merged.append([a, b])
        elif b > merged[-1][1]:
            merged[-1][1] = b
    return [(a, b) for a, b in merged]


def interval_complement(base: Tuple[Fraction, Fraction], merged: Sequence[Tuple[Fraction, Fraction]]) -> List[Tuple[Fraction, Fraction]]:
    lo, hi = base
    cur = lo
    out: List[Tuple[Fraction, Fraction]] = []
    for a, b in merged:
        aa = max(a, lo)
        bb = min(b, hi)
        if bb <= aa:
            continue
        if cur < aa:
            out.append((cur, aa))
        if bb > cur:
            cur = bb
    if cur < hi:
        out.append((cur, hi))
    return out


def lcm_list(vals: Iterable[int]) -> int:
    return reduce(lcm, vals, 1)


def count_integer_points(L: int, a: Fraction, b: Fraction) -> int:
    """Count integers x with a <= x/L < b."""
    lo = (a.numerator * L + a.denominator - 1) // a.denominator
    hi = ((b.numerator * L + b.denominator - 1) // b.denominator) - 1
    return max(0, hi - lo + 1)


@dataclass
class Row:
    n: int
    dropped_a: int
    dropped_b: int
    e_max: int
    best_r: int
    best_miss: Fraction
    bound: Fraction
    ratio: Fraction
    den_max: int
    L0: int
    max_b_count_m1: int
    caseB_Gtot: int
    caseB_thresh: int
    best_miss_touches_boundary: int


def analyze_template(n: int, dropped: Tuple[int, int]) -> Row | None:
    E_fix = [e for e in range(1, n) if e not in dropped]
    E_nu = [e for e in E_fix if gcd(e, n) > 1]
    g_tot = sum(gcd(e, n) for e in E_nu)
    thresh = 1 + 2 * len(E_nu)
    # Case-B
    if g_tot <= thresh:
        return None

    # Case-iiib preconditions
    if 1 not in E_fix or (n - 1) not in E_fix:
        return None

    U0: set[int] = set()
    for e in E_fix:
        U0 |= bad_set(e, 0, n)
    if len(U0) < n:
        return None

    I_div = (Fraction(1, n), Fraction(n - 1, n))

    best_r = -1
    best_m = Fraction(-1, 1)
    best_miss_intervals: List[Tuple[Fraction, Fraction]] = []

    for r in range(n):
        cov: List[Tuple[Fraction, Fraction]] = []
        for e in E_fix:
            for t in range(e):
                if r in bad_set(e, t, n):
                    a, b = Fraction(t, e), Fraction(t + 1, e)
                    aa = max(a, I_div[0])
                    bb = min(b, I_div[1])
                    if aa < bb:
                        cov.append((aa, bb))

        merged = merge_intervals(cov)
        miss = interval_complement(I_div, merged)
        m = sum((b - a) for a, b in miss)
        if m > best_m:
            best_m = m
            best_r = r
            best_miss_intervals = miss

    e_max = max(E_fix)
    bound = Fraction(1, e_max * (e_max - 1))
    ratio = best_m / bound

    den_max = 0
    for a, b in best_miss_intervals:
        den_max = max(den_max, a.denominator, b.denominator)

    L0 = lcm_list(E_fix + [n])
    max_b_count = 0
    for a, b in best_miss_intervals:
        max_b_count = max(max_b_count, count_integer_points(L0, a, b))

    touches_boundary = 0
    for a, b in best_miss_intervals:
        if a == I_div[0] or b == I_div[1]:
            touches_boundary = 1
            break

    return Row(
        n=n,
        dropped_a=dropped[0],
        dropped_b=dropped[1],
        e_max=e_max,
        best_r=best_r,
        best_miss=best_m,
        bound=bound,
        ratio=ratio,
        den_max=den_max,
        L0=L0,
        max_b_count_m1=max_b_count,
        caseB_Gtot=g_tot,
        caseB_thresh=thresh,
        best_miss_touches_boundary=touches_boundary,
    )


def is_composite(n: int) -> bool:
    if n < 4:
        return False
    for p in range(2, int(n ** 0.5) + 1):
        if n % p == 0:
            return True
    return False


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n-min", type=int, default=10)
    ap.add_argument("--n-max", type=int, default=30)
    ap.add_argument("--out-csv", type=Path, default=Path("/tmp/lrc_sl1b_extended_probe_rows_v1.csv"))
    ap.add_argument("--out-summary", type=Path, default=Path("/tmp/lrc_sl1b_extended_probe_summary_v1.md"))
    args = ap.parse_args()

    rows: List[Row] = []
    for n in range(args.n_min, args.n_max + 1):
        if not is_composite(n):
            continue
        for dropped in combinations(range(1, n), 2):
            row = analyze_template(n, dropped)
            if row is not None:
                rows.append(row)

    args.out_csv.parent.mkdir(parents=True, exist_ok=True)
    with args.out_csv.open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow(
            [
                "n",
                "dropped_a",
                "dropped_b",
                "e_max",
                "best_r",
                "best_miss",
                "bound",
                "ratio",
                "den_max",
                "L0",
                "max_b_count_m1",
                "caseB_Gtot",
                "caseB_thresh",
                "best_miss_touches_boundary",
            ]
        )
        for r in rows:
            w.writerow(
                [
                    r.n,
                    r.dropped_a,
                    r.dropped_b,
                    r.e_max,
                    r.best_r,
                    f"{r.best_miss.numerator}/{r.best_miss.denominator}",
                    f"{r.bound.numerator}/{r.bound.denominator}",
                    f"{float(r.ratio):.12f}",
                    r.den_max,
                    r.L0,
                    r.max_b_count_m1,
                    r.caseB_Gtot,
                    r.caseB_thresh,
                    r.best_miss_touches_boundary,
                ]
            )

    violations = [r for r in rows if r.best_miss < r.bound]
    den_viol = [r for r in rows if r.den_max > r.n]
    zero_b = [r for r in rows if r.max_b_count_m1 <= 0]
    touch_rows = [r for r in rows if r.best_miss_touches_boundary == 1]

    by_n: dict[int, List[Row]] = {}
    for r in rows:
        by_n.setdefault(r.n, []).append(r)

    lines: List[str] = []
    lines.append("# SL-1.B Extended Probe Summary (v1)")
    lines.append("")
    lines.append(f"Range: composite n in [{args.n_min}, {args.n_max}]")
    lines.append(f"Case-iiib templates checked: {len(rows)}")
    lines.append("")
    lines.append("## Global checks")
    lines.append("")
    lines.append(f"- Bound violations (best_miss < 1/(e_max*(e_max-1))): {len(violations)}")
    lines.append(f"- Denominator violations (den_max > n): {len(den_viol)}")
    lines.append(f"- Zero integer witness at M=1 (max_b_count_m1 <= 0): {len(zero_b)}")
    lines.append(f"- Best miss interval touches I_div boundary: {len(touch_rows)}")
    lines.append("")

    if rows:
        min_ratio = min(rows, key=lambda r: r.ratio)
        min_b = min(rows, key=lambda r: r.max_b_count_m1)
        lines.append("## Extremal rows")
        lines.append("")
        lines.append(
            "- Min ratio row: "
            f"n={min_ratio.n}, dropped=({min_ratio.dropped_a},{min_ratio.dropped_b}), "
            f"best_r={min_ratio.best_r}, best_miss={min_ratio.best_miss}, bound={min_ratio.bound}, "
            f"ratio={float(min_ratio.ratio):.12f}"
        )
        lines.append(
            "- Min integer witness row (M=1): "
            f"n={min_b.n}, dropped=({min_b.dropped_a},{min_b.dropped_b}), "
            f"max_b_count_m1={min_b.max_b_count_m1}, L0={min_b.L0}"
        )
        lines.append("")

    lines.append("## Per-n summary")
    lines.append("")
    lines.append("| n | templates | min_ratio | min_best_miss | min_max_b_count_m1 |")
    lines.append("|---:|---:|---:|---:|---:|")
    for n in sorted(by_n):
        rr = by_n[n]
        mn_ratio = min(rr, key=lambda r: r.ratio).ratio
        mn_miss = min(rr, key=lambda r: r.best_miss).best_miss
        mn_bc = min(rr, key=lambda r: r.max_b_count_m1).max_b_count_m1
        lines.append(
            f"| {n} | {len(rr)} | {float(mn_ratio):.6f} | {mn_miss.numerator}/{mn_miss.denominator} | {mn_bc} |"
        )

    args.out_summary.parent.mkdir(parents=True, exist_ok=True)
    args.out_summary.write_text("\n".join(lines) + "\n")

    print(f"wrote csv: {args.out_csv}")
    print(f"wrote summary: {args.out_summary}")


if __name__ == "__main__":
    main()
