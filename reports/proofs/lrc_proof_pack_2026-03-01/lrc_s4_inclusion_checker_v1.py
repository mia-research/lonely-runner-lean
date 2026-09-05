#!/usr/bin/env python3
from __future__ import annotations

from fractions import Fraction
import csv
import math
from functools import lru_cache
from itertools import combinations, product
from collections import Counter, defaultdict

import numpy as np
from scipy.optimize import linprog

OUT_TABLE = "/tmp/lrc_s4_inclusion_table_v1.csv"
OUT_SUMMARY = "/tmp/lrc_s4_inclusion_summary_v1.md"
OUT_UNRES = "/tmp/lrc_s4_unresolved_families_v1.csv"

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


def comb4(x: int) -> int:
    return x * (x - 1) * (x - 2) * (x - 3) // 24


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
    S4 = sum(comb4(m) for m in mult)
    safe = sum(1 for m in mult if m == 0)
    union = N - safe
    return {
        "L": L,
        "N": N,
        "S1": S1,
        "S2": S2,
        "S3": S3,
        "S4": S4,
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


def k_overlap_formula(e_tuple: tuple[int, ...], n: int, L: int) -> int:
    # Exact CRT-lift count for intersection of dangerous sets in e_tuple.
    g = 0
    for e in e_tuple:
        g = math.gcd(g, e)
    M = (n * L) // g
    cnt = 0
    for x in range(M):
        ok = True
        for e in e_tuple:
            if not danger_mod_x(e, n, L, x):
                ok = False
                break
        if ok:
            cnt += 1
    return g * cnt


def formula_moments(e_list: tuple[int, ...], n: int):
    L = math.lcm(*e_list)
    N = n * L

    S1 = sum(single_formula(e, n, L) for e in e_list)
    S2 = sum(pair_formula(a, b, n, L) for a, b in combinations(e_list, 2))
    S3 = sum(k_overlap_formula((a, b, c), n, L) for a, b, c in combinations(e_list, 3))
    S4 = sum(k_overlap_formula((a, b, c, d), n, L) for a, b, c, d in combinations(e_list, 4))

    return {"L": L, "N": N, "S1": S1, "S2": S2, "S3": S3, "S4": S4}


def lp_min_x0(max_mult: int, N: int, S1: int, S2: int | None = None, S3: int | None = None, S4: int | None = None) -> float:
    # Variables x_r >=0 for multiplicity histogram at r=0..max_mult.
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

    if S4 is not None:
        A_eq.append([float(comb4(r)) for r in range(cols)])
        b_eq.append(float(S4))

    res = linprog(
        c=c,
        A_eq=np.array(A_eq, dtype=float),
        b_eq=np.array(b_eq, dtype=float),
        bounds=[(0.0, None)] * cols,
        method="highs",
    )

    if not res.success:
        return float("nan")
    return float(res.fun)


def verify_formulas(samples: int = 200):
    import random

    random.seed(0)
    for _ in range(samples):
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
        assert f["S4"] == b["S4"], (n, e, f["S4"], b["S4"])


def residue_signature(e_list: tuple[int, ...], n: int) -> str:
    arr = sorted([e % n for e in e_list])
    return " ".join(map(str, arr))


def run_scan():
    rows = []
    summary = []
    unresolved_rows = []

    for n in sorted(MAX_E_BY_N):
        max_e = MAX_E_BY_N[n]

        tuples_total = 0
        tuples_gcd1 = 0
        proven_s2 = 0
        proven_s3 = 0
        proven_s4 = 0

        unresolved_s3 = 0
        unresolved_s4 = 0

        for e_tuple in product(range(1, max_e + 1), repeat=n - 1):
            tuples_total += 1
            if math.gcd(*e_tuple) != 1:
                continue
            tuples_gcd1 += 1

            f = formula_moments(e_tuple, n)
            b = brute_profile(e_tuple, n)

            lp2 = lp_min_x0(n - 1, f["N"], f["S1"], f["S2"], None, None)
            lp3 = lp_min_x0(n - 1, f["N"], f["S1"], f["S2"], f["S3"], None)
            lp4 = lp_min_x0(n - 1, f["N"], f["S1"], f["S2"], f["S3"], f["S4"])

            p2 = lp2 > 1e-9
            p3 = lp3 > 1e-9
            p4 = lp4 > 1e-9

            if p2:
                proven_s2 += 1
            if p3:
                proven_s3 += 1
            if p4:
                proven_s4 += 1

            if not p3:
                unresolved_s3 += 1
            if not p4:
                unresolved_s4 += 1

            row = {
                "n": n,
                "max_e": max_e,
                "e_tuple": " ".join(map(str, e_tuple)),
                "sorted_tuple": " ".join(map(str, sorted(e_tuple))),
                "residue_sig_mod_n": residue_signature(e_tuple, n),
                "L": f["L"],
                "N": f["N"],
                "safe_count": b["safe_count"],
                "S1": f["S1"],
                "S2": f["S2"],
                "S3": f["S3"],
                "S4": f["S4"],
                "lp_min_x0_S1S2": f"{lp2:.12f}",
                "lp_min_x0_S1S2S3": f"{lp3:.12f}",
                "lp_min_x0_S1S2S3S4": f"{lp4:.12f}",
                "proven_s2": int(p2),
                "proven_s3": int(p3),
                "proven_s4": int(p4),
            }
            rows.append(row)

            if n in (5, 6) and (not p4):
                unresolved_rows.append(row)

        summary.append(
            {
                "n": n,
                "max_e": max_e,
                "tuples_gcd1": tuples_gcd1,
                "proven_s2": proven_s2,
                "proven_s3": proven_s3,
                "proven_s4": proven_s4,
                "rate_s2": proven_s2 / tuples_gcd1 if tuples_gcd1 else 0.0,
                "rate_s3": proven_s3 / tuples_gcd1 if tuples_gcd1 else 0.0,
                "rate_s4": proven_s4 / tuples_gcd1 if tuples_gcd1 else 0.0,
                "unresolved_s3": unresolved_s3,
                "unresolved_s4": unresolved_s4,
            }
        )

    return rows, summary, unresolved_rows


def write_outputs(rows, summary, unresolved_rows):
    with open(OUT_TABLE, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    # Unresolved family aggregation for n=5,6 under S4
    fam_counter = Counter()
    for r in unresolved_rows:
        key = (int(r["n"]), r["sorted_tuple"], r["residue_sig_mod_n"], int(r["L"]), int(r["safe_count"]))
        fam_counter[key] += 1

    with open(OUT_UNRES, "w", newline="") as f:
        fieldnames = [
            "n",
            "sorted_tuple",
            "residue_sig_mod_n",
            "L",
            "safe_count",
            "count",
        ]
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        for (n, s, rs, L, sc), cnt in sorted(fam_counter.items()):
            w.writerow(
                {
                    "n": n,
                    "sorted_tuple": s,
                    "residue_sig_mod_n": rs,
                    "L": L,
                    "safe_count": sc,
                    "count": cnt,
                }
            )

    lines = []
    lines.append("# S4 Inclusion Checker (v1)")
    lines.append("")
    lines.append("Exact moments used: S1, S2, S3, S4 (all verified against brute profiles).")
    lines.append("")
    lines.append("| n | max_e | gcd1 tuples | proven S1,S2 | proven S1,S2,S3 | proven S1,S2,S3,S4 | rate S2 | rate S3 | rate S4 | unresolved S3 | unresolved S4 |")
    lines.append("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    for r in summary:
        lines.append(
            f"| {r['n']} | {r['max_e']} | {r['tuples_gcd1']} | {r['proven_s2']} | {r['proven_s3']} | {r['proven_s4']} | "
            f"{r['rate_s2']:.4f} | {r['rate_s3']:.4f} | {r['rate_s4']:.4f} | {r['unresolved_s3']} | {r['unresolved_s4']} |"
        )

    lines.append("")
    lines.append("Artifacts:")
    lines.append(f"- table: `{OUT_TABLE}`")
    lines.append(f"- unresolved families (`n=5,6`, S4 unresolved): `{OUT_UNRES}`")
    lines.append(f"- summary: `{OUT_SUMMARY}`")

    with open(OUT_SUMMARY, "w") as f:
        f.write("\n".join(lines) + "\n")


def main():
    verify_formulas(250)
    rows, summary, unresolved_rows = run_scan()
    write_outputs(rows, summary, unresolved_rows)
    print("FINAL")
    print("table", OUT_TABLE)
    print("unresolved", OUT_UNRES)
    print("summary", OUT_SUMMARY)


if __name__ == "__main__":
    main()
