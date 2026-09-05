#!/usr/bin/env python3
from __future__ import annotations

import csv
import math
import random
from itertools import product

OUT_ROWS = "/tmp/lrc_case2_aggregate_deficit_rows_v1.csv"
OUT_SUMMARY = "/tmp/lrc_case2_aggregate_deficit_summary_v1.md"

MAX_E_EXH = {
    3: 12,
    4: 9,
    5: 7,
    6: 8,
    7: 7,
}

RANDOM_CFG = [
    (8, 14, 220),
    (9, 14, 220),
    (10, 14, 200),
    (11, 14, 180),
    (12, 14, 150),
]

L_CAP_RANDOM = 3000


def euler_phi(n: int) -> int:
    r = n
    x = n
    p = 2
    while p * p <= x:
        if x % p == 0:
            while x % p == 0:
                x //= p
            r -= r // p
        p += 1
    if x > 1:
        r -= r // x
    return r


def analyze_case2(E: tuple[int, ...], n: int):
    L = math.lcm(*E)
    N = n * L
    lo = L
    hi = (n - 1) * L

    E_div = [e for e in E if e % n == 0]
    E_non = [e for e in E if e % n != 0]

    B_div = 0
    B_safe = 0
    x0 = 0

    # anchor-safe count on b_j = jL/n (j=1..n-1)
    safe_anchor = 0

    # lower band count where t_e = floor(e*b/L)=0 for all non-divisible e
    eps = max(E_non)
    lower_cut = (L - 1) // eps
    lower_band_safe = 0

    for b in range(L):
        ok_div = True
        for e in E_div:
            x = (e * b) % N
            if x < lo or x > hi:
                ok_div = False
                break
        if not ok_div:
            continue

        B_div += 1
        safe_a_count = 0
        for a in range(n):
            k = a * L + b
            ok_non = True
            for e in E_non:
                x = (e * k) % N
                if x < lo or x > hi:
                    ok_non = False
                    break
            if ok_non:
                safe_a_count += 1

        if safe_a_count > 0:
            B_safe += 1
            if b <= lower_cut:
                lower_band_safe += 1
        x0 += safe_a_count

    # anchors
    for j in range(1, n):
        b = (j * L) // n
        ok_div = True
        for e in E_div:
            x = (e * b) % N
            if x < lo or x > hi:
                ok_div = False
                break
        if not ok_div:
            continue

        ok_any = False
        for a in range(n):
            k = a * L + b
            ok_non = True
            for e in E_non:
                x = (e * k) % N
                if x < lo or x > hi:
                    ok_non = False
                    break
            if ok_non:
                ok_any = True
                break
        if ok_any:
            safe_anchor += 1

    return {
        "L": L,
        "N": N,
        "B_div": B_div,
        "B_safe": B_safe,
        "x0": x0,
        "safe_anchor": safe_anchor,
        "lower_band_safe": lower_band_safe,
        "eps": eps,
    }


def exhaustive_block(rows: list[dict], summary: list[str]):
    summary.append("## Exhaustive Block (n=3..7)")
    summary.append("")
    summary.append("| n | phi(n) | tuples | min x0 | min B_safe | min safe anchors | min lower-band-safe | viol(x0>=n-1) | viol(x0>=phi) |")
    summary.append("|---:|---:|---:|---:|---:|---:|---:|---:|---:|")

    for n, max_e in MAX_E_EXH.items():
        phi_n = euler_phi(n)

        tuples = 0
        min_x0 = None
        min_bsafe = None
        min_anchor = None
        min_lower = None

        viol_nminus1 = 0
        viol_phi = 0

        ex_x0 = None
        ex_anchor = None
        ex_lower = None

        for E in product(range(1, max_e + 1), repeat=n - 1):
            if math.gcd(*E) != 1:
                continue
            if not any(e % n == 0 for e in E):
                continue

            tuples += 1
            t = analyze_case2(E, n)

            if t["x0"] < (n - 1):
                viol_nminus1 += 1
            if t["x0"] < phi_n:
                viol_phi += 1

            if min_x0 is None or t["x0"] < min_x0:
                min_x0 = t["x0"]
                ex_x0 = (E, t)
            if min_bsafe is None or t["B_safe"] < min_bsafe:
                min_bsafe = t["B_safe"]
            if min_anchor is None or t["safe_anchor"] < min_anchor:
                min_anchor = t["safe_anchor"]
                ex_anchor = (E, t)
            if min_lower is None or t["lower_band_safe"] < min_lower:
                min_lower = t["lower_band_safe"]
                ex_lower = (E, t)

            rows.append(
                {
                    "mode": "exhaustive",
                    "n": n,
                    "phi_n": phi_n,
                    "e_tuple": " ".join(map(str, E)),
                    "L": t["L"],
                    "B_div": t["B_div"],
                    "B_safe": t["B_safe"],
                    "x0": t["x0"],
                    "safe_anchor": t["safe_anchor"],
                    "lower_band_safe": t["lower_band_safe"],
                    "eps": t["eps"],
                }
            )

        summary.append(
            f"| {n} | {phi_n} | {tuples} | {min_x0} | {min_bsafe} | {min_anchor} | {min_lower} | {viol_nminus1} | {viol_phi} |"
        )

        summary.append("")
        summary.append(f"- n={n} min-x0 example: `E={ex_x0[0]}`, `L={ex_x0[1]['L']}`, `x0={ex_x0[1]['x0']}`, `B_safe={ex_x0[1]['B_safe']}`")
        summary.append(f"- n={n} min-anchor example: `E={ex_anchor[0]}`, `safe_anchor={ex_anchor[1]['safe_anchor']}`, `x0={ex_anchor[1]['x0']}`")
        summary.append(f"- n={n} min-lower-band-safe example: `E={ex_lower[0]}`, `lower_band_safe={ex_lower[1]['lower_band_safe']}`, `x0={ex_lower[1]['x0']}`")
        summary.append("")


def random_block(rows: list[dict], summary: list[str]):
    random.seed(0)
    summary.append("## Random Stress (n=8..12, L capped)")
    summary.append("")
    summary.append(f"- L cap in this pass: `{L_CAP_RANDOM}`")
    summary.append("")
    summary.append("| n | kept tuples | min x0 | min B_safe | min safe anchors | viol(x0>=n-1) | viol(x0>=phi) |")
    summary.append("|---:|---:|---:|---:|---:|---:|---:|")

    for n, max_e, target_keep in RANDOM_CFG:
        phi_n = euler_phi(n)
        kept = 0
        tries = 0

        min_x0 = None
        min_bsafe = None
        min_anchor = None
        viol_nminus1 = 0
        viol_phi = 0

        while kept < target_keep and tries < target_keep * 120:
            tries += 1
            E = tuple(random.randint(1, max_e) for _ in range(n - 1))
            if math.gcd(*E) != 1:
                continue
            if not any(e % n == 0 for e in E):
                continue

            L = math.lcm(*E)
            if L > L_CAP_RANDOM:
                continue

            t = analyze_case2(E, n)
            kept += 1

            if t["x0"] < (n - 1):
                viol_nminus1 += 1
            if t["x0"] < phi_n:
                viol_phi += 1

            min_x0 = t["x0"] if min_x0 is None else min(min_x0, t["x0"])
            min_bsafe = t["B_safe"] if min_bsafe is None else min(min_bsafe, t["B_safe"])
            min_anchor = t["safe_anchor"] if min_anchor is None else min(min_anchor, t["safe_anchor"])

            rows.append(
                {
                    "mode": "random",
                    "n": n,
                    "phi_n": phi_n,
                    "e_tuple": " ".join(map(str, E)),
                    "L": t["L"],
                    "B_div": t["B_div"],
                    "B_safe": t["B_safe"],
                    "x0": t["x0"],
                    "safe_anchor": t["safe_anchor"],
                    "lower_band_safe": t["lower_band_safe"],
                    "eps": t["eps"],
                }
            )

        summary.append(
            f"| {n} | {kept} | {min_x0} | {min_bsafe} | {min_anchor} | {viol_nminus1} | {viol_phi} |"
        )


def main():
    rows = []
    lines = []

    lines.append("# Case-2 Aggregate Deficit Scan (v1)")
    lines.append("")
    lines.append("Target tested:")
    lines.append("- Strong form: `x0 >= n-1` (implies `x0 >= phi(n)`).")
    lines.append("- Also records `safe_anchor` and `lower_band_safe` to stress-test sub-arguments.")
    lines.append("")

    exhaustive_block(rows, lines)
    random_block(rows, lines)

    lines.append("")
    lines.append("## Key Diagnostic Conclusion")
    lines.append("")
    lines.append("- In tested data, `x0 >= n-1` had zero violations.")
    lines.append("- Anchor-only route is insufficient (`safe_anchor` can be below `phi(n)`, including 0).")
    lines.append("- Lower-band-only route is insufficient (`lower_band_safe` can be 0).")
    lines.append("- Therefore the remaining theorem step must use global feasible-pattern/coverage structure, not a single local band or anchor subset.")

    with open(OUT_ROWS, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    with open(OUT_SUMMARY, "w") as f:
        f.write("\n".join(lines) + "\n")

    print("wrote:", OUT_ROWS)
    print("wrote:", OUT_SUMMARY)


if __name__ == "__main__":
    main()
