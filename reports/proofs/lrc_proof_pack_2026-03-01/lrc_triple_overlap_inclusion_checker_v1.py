#!/usr/bin/env python3
from __future__ import annotations

from fractions import Fraction
import csv
import math
from functools import lru_cache
from itertools import combinations, product
from typing import Iterable

import numpy as np
from scipy.optimize import linprog

OUT_SUMMARY = "/tmp/lrc_triple_overlap_inclusion_summary_v1.md"
OUT_TABLE = "/tmp/lrc_triple_overlap_inclusion_table_v1.csv"

MAX_E_BY_N = {
    3: 12,
    4: 9,
    5: 7,
    6: 5,
    7: 4,
    8: 4,
}


def comb2(x: int) -> int:
    return x * (x - 1) // 2


def comb3(x: int) -> int:
    return x * (x - 1) * (x - 2) // 6


def danger_indicator(e: int, n: int, N: int, k: int) -> int:
    v = (e * Fraction(k, N)) % 1
    return int(not (Fraction(1, n) <= v <= Fraction(n - 1, n)))


def brute_profile(e_list: tuple[int, ...], n: int):
    L = math.lcm(*e_list)
    N = n * L
    mult = [0] * N
    for e in e_list:
        for k in range(N):
            mult[k] += danger_indicator(e, n, N, k)

    S1 = sum(mult)
    S2 = sum(comb2(m) for m in mult)
    S3 = sum(comb3(m) for m in mult)
    safe = sum(1 for m in mult if m == 0)
    union = N - safe
    return {
        "L": L,
        "N": N,
        "S1": S1,
        "S2": S2,
        "S3": S3,
        "safe_count": safe,
        "union": union,
    }


def count_residue_in_interval(lo: int, hi: int, r: int, d: int) -> int:
    if lo > hi:
        return 0
    x = lo + ((r - lo) % d)
    if x > hi:
        return 0
    return 1 + (hi - x) // d


def c_count(e: int, n: int, L: int, r: int, d: int) -> int:
    p = L // e
    m = n * p
    low = count_residue_in_interval(0, p - 1, r, d)
    high = count_residue_in_interval(m - p + 1, m - 1, r, d)
    return low + high


@lru_cache(maxsize=None)
def single_formula(e: int, n: int, L: int) -> int:
    return 2 * L - e


@lru_cache(maxsize=None)
def pair_formula(a: int, b: int, n: int, L: int) -> int:
    ma = n * (L // a)
    mb = n * (L // b)
    d = math.gcd(ma, mb)
    g = math.gcd(a, b)

    total = 0
    for r in range(d):
        total += c_count(a, n, L, r, d) * c_count(b, n, L, r, d)
    return g * total


def danger_mod_x(e: int, n: int, L: int, x: int) -> bool:
    p = L // e
    m = n * p
    r = x % m
    return (r < p) or (r > (m - p))


@lru_cache(maxsize=None)
def triple_formula(a: int, b: int, c: int, n: int, L: int) -> int:
    # Exact CRT-lift formula:
    # |D_a∩D_b∩D_c| = g * #{x mod M : x in all three dangerous residue systems}
    # where g=gcd(a,b,c), M=nL/g.
    g = math.gcd(math.gcd(a, b), c)
    M = (n * L) // g

    cnt = 0
    for x in range(M):
        if danger_mod_x(a, n, L, x) and danger_mod_x(b, n, L, x) and danger_mod_x(c, n, L, x):
            cnt += 1
    return g * cnt


def formula_moments(e_list: tuple[int, ...], n: int):
    L = math.lcm(*e_list)
    N = n * L

    S1 = sum(single_formula(e, n, L) for e in e_list)
    S2 = sum(pair_formula(a, b, n, L) for a, b in combinations(e_list, 2))
    S3 = sum(triple_formula(a, b, c, n, L) for a, b, c in combinations(e_list, 3))

    return {"L": L, "N": N, "S1": S1, "S2": S2, "S3": S3}


def lp_min_x0(max_mult: int, N: int, S1: int, S2: int | None = None, S3: int | None = None) -> float:
    # Variables x_r = number of lattice points with multiplicity r, r=0..max_mult.
    # Minimize x_0 subject to moment equalities.
    cols = max_mult + 1
    c = np.zeros(cols, dtype=float)
    c[0] = 1.0

    A_eq = []
    b_eq = []

    A_eq.append([1.0] * cols)
    b_eq.append(float(N))

    A_eq.append([float(r) for r in range(cols)])
    b_eq.append(float(S1))

    if S2 is not None:
        A_eq.append([float(comb2(r)) for r in range(cols)])
        b_eq.append(float(S2))

    if S3 is not None:
        A_eq.append([float(comb3(r)) for r in range(cols)])
        b_eq.append(float(S3))

    bounds = [(0.0, None)] * cols

    res = linprog(
        c=c,
        A_eq=np.array(A_eq, dtype=float),
        b_eq=np.array(b_eq, dtype=float),
        bounds=bounds,
        method="highs",
    )

    if not res.success:
        return float("nan")
    return float(res.fun)


def verify_formulas() -> None:
    # Verify S1/S2/S3 formulas against brute profile on random small cases.
    import random

    random.seed(0)
    for _ in range(200):
        n = random.randint(3, 8)
        e = tuple(random.randint(1, 8) for _ in range(n - 1))
        if math.gcd(*e) != 1:
            continue
        f = formula_moments(e, n)
        b = brute_profile(e, n)
        assert f["N"] == b["N"]
        assert f["S1"] == b["S1"], (n, e, f["S1"], b["S1"])
        assert f["S2"] == b["S2"], (n, e, f["S2"], b["S2"])
        assert f["S3"] == b["S3"], (n, e, f["S3"], b["S3"])


def run_scan():
    rows = []
    summary = []

    for n in sorted(MAX_E_BY_N):
        max_e = MAX_E_BY_N[n]

        tuples_total = 0
        tuples_gcd1 = 0

        proven_s2 = 0
        proven_s3 = 0

        min_gap_s2 = None
        min_gap_s3 = None

        for e_tuple in product(range(1, max_e + 1), repeat=n - 1):
            tuples_total += 1
            if math.gcd(*e_tuple) != 1:
                continue
            tuples_gcd1 += 1

            f = formula_moments(e_tuple, n)
            b = brute_profile(e_tuple, n)

            lp2 = lp_min_x0(n - 1, f["N"], f["S1"], f["S2"], None)
            lp3 = lp_min_x0(n - 1, f["N"], f["S1"], f["S2"], f["S3"])

            # Lower bound gap to true safe count
            gap2 = b["safe_count"] - lp2
            gap3 = b["safe_count"] - lp3

            if min_gap_s2 is None or gap2 < min_gap_s2:
                min_gap_s2 = gap2
            if min_gap_s3 is None or gap3 < min_gap_s3:
                min_gap_s3 = gap3

            if lp2 > 1e-9:
                proven_s2 += 1
            if lp3 > 1e-9:
                proven_s3 += 1

            rows.append(
                {
                    "n": n,
                    "max_e": max_e,
                    "e_tuple": " ".join(map(str, e_tuple)),
                    "L": f["L"],
                    "N": f["N"],
                    "safe_count": b["safe_count"],
                    "S1": f["S1"],
                    "S2": f["S2"],
                    "S3": f["S3"],
                    "lp_min_x0_S1S2": f"{lp2:.12f}",
                    "lp_min_x0_S1S2S3": f"{lp3:.12f}",
                }
            )

        summary.append(
            {
                "n": n,
                "max_e": max_e,
                "tuples_gcd1": tuples_gcd1,
                "proven_s2": proven_s2,
                "proven_s3": proven_s3,
                "prove_rate_s2": proven_s2 / tuples_gcd1 if tuples_gcd1 else 0.0,
                "prove_rate_s3": proven_s3 / tuples_gcd1 if tuples_gcd1 else 0.0,
                "min_gap_s2": min_gap_s2 if min_gap_s2 is not None else float("nan"),
                "min_gap_s3": min_gap_s3 if min_gap_s3 is not None else float("nan"),
            }
        )

    return rows, summary


def write_outputs(rows, summary):
    if rows:
        with open(OUT_TABLE, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
            w.writeheader()
            w.writerows(rows)

    lines = []
    lines.append("# Triple-Overlap + Inclusion Checker (v1)")
    lines.append("")
    lines.append("Formulas used:")
    lines.append("- `|D_e| = 2L - e`")
    lines.append("- Pair overlap: exact CRT residue formula")
    lines.append("- Triple overlap: exact CRT-lift formula")
    lines.append("  `|D_a∩D_b∩D_c| = g * #{x mod M : x in all three dangerous residue systems}`")
    lines.append("  where `g=gcd(a,b,c)`, `M=nL/g`.")
    lines.append("")
    lines.append("LP bounds:")
    lines.append("- `lp_min_x0_S1S2`: min possible safe-point count from moments (N,S1,S2)")
    lines.append("- `lp_min_x0_S1S2S3`: min possible safe-point count from moments (N,S1,S2,S3)")
    lines.append("- If lower bound > 0, then `|U D_e| < N` is proven for that tuple by those moments.")
    lines.append("")
    lines.append("| n | max_e | gcd1 tuples | proven (S1,S2) | proven (S1,S2,S3) | rate S1,S2 | rate S1,S2,S3 |")
    lines.append("|---:|---:|---:|---:|---:|---:|---:|")
    for r in summary:
        lines.append(
            f"| {r['n']} | {r['max_e']} | {r['tuples_gcd1']} | {r['proven_s2']} | {r['proven_s3']} | {r['prove_rate_s2']:.4f} | {r['prove_rate_s3']:.4f} |"
        )

    lines.append("")
    lines.append("Artifacts:")
    lines.append(f"- table: `{OUT_TABLE}`")
    lines.append(f"- summary: `{OUT_SUMMARY}`")

    with open(OUT_SUMMARY, "w") as f:
        f.write("\n".join(lines) + "\n")


def main():
    verify_formulas()
    rows, summary = run_scan()
    write_outputs(rows, summary)

    print("FINAL")
    print("table", OUT_TABLE)
    print("summary", OUT_SUMMARY)


if __name__ == "__main__":
    main()
