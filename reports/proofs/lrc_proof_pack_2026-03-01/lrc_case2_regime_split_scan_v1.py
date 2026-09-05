#!/usr/bin/env python3
from __future__ import annotations

import csv
import math
import random
from itertools import product

OUT_ROWS = "/tmp/lrc_case2_regime_split_rows_v1.csv"
OUT_SUMMARY = "/tmp/lrc_case2_regime_split_summary_v1.md"

MAX_E_BY_N = {
    3: 12,
    4: 9,
    5: 7,
    6: 8,
    7: 7,
}


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


def eval_case2_tuple(E: tuple[int, ...], n: int):
    L = math.lcm(*E)
    N = n * L
    lo = L
    hi = (n - 1) * L

    E_div = [e for e in E if e % n == 0]
    E_non = [e for e in E if e % n != 0]

    B_div = [b for b in range(L) if all(lo <= (e * b) % N <= hi for e in E_div)]

    C_bad = 0
    B_safe = 0
    x0 = 0

    for b in B_div:
        bad_fiber = True
        for a in range(n):
            k = a * L + b
            any_bad = False
            for e in E_non:
                r = (e * k) % N
                if r < lo or r > hi:
                    any_bad = True
                    break
            if not any_bad:
                bad_fiber = False
                break

        if bad_fiber:
            C_bad += 1
        else:
            B_safe += 1
            for a in range(n):
                k = a * L + b
                if all(lo <= (e * k) % N <= hi for e in E_non):
                    x0 += 1

    return {
        "L": L,
        "N": N,
        "B_div": len(B_div),
        "C_bad": C_bad,
        "B_safe": B_safe,
        "x0": x0,
    }


def main() -> None:
    rows = []
    lines = []

    lines.append("# Case-2 Regime Split Scan (v1)")
    lines.append("")
    lines.append("Regimes:")
    lines.append("- Anchor regime: `L=n`")
    lines.append("- Slack regime: `L>n`")
    lines.append("")

    # Canonical family check
    lines.append("## Canonical family `(1,...,1,n)`")
    lines.append("| n | tuple | L | B_div | C_bad | B_safe | x0 | phi(n) |")
    lines.append("|---:|---|---:|---:|---:|---:|---:|---:|")
    for n in range(3, 8):
        E = tuple([1] * (n - 2) + [n])
        t = eval_case2_tuple(E, n)
        lines.append(
            f"| {n} | `{E}` | {t['L']} | {t['B_div']} | {t['C_bad']} | {t['B_safe']} | {t['x0']} | {euler_phi(n)} |"
        )

    lines.append("")
    lines.append("## Exhaustive bounded Case-2 grids")
    lines.append("| n | tuples | min B_safe overall | min B_safe (L=n) | min B_safe (L>n) | tight count (B_safe=n-1) | tight with L=n | tight profile mismatches |")
    lines.append("|---:|---:|---:|---:|---:|---:|---:|---:|")

    for n, max_e in MAX_E_BY_N.items():
        total = 0
        min_all = None
        min_Ln = None
        min_Lgt = None

        tight = 0
        tight_Ln = 0
        tight_profile_mismatch = 0

        for E in product(range(1, max_e + 1), repeat=n - 1):
            if math.gcd(*E) != 1:
                continue
            if not any(e % n == 0 for e in E):
                continue

            total += 1
            t = eval_case2_tuple(E, n)
            L = t["L"]
            B_safe = t["B_safe"]
            B_div = t["B_div"]
            C_bad = t["C_bad"]

            if min_all is None or B_safe < min_all:
                min_all = B_safe
            if L == n:
                if min_Ln is None or B_safe < min_Ln:
                    min_Ln = B_safe
            else:
                if min_Lgt is None or B_safe < min_Lgt:
                    min_Lgt = B_safe

            if B_safe == n - 1:
                tight += 1
                if L == n:
                    tight_Ln += 1
                if not (L == n and B_div == n - 1 and C_bad == 0):
                    tight_profile_mismatch += 1

            rows.append(
                {
                    "n": n,
                    "e_tuple": " ".join(map(str, E)),
                    "L": L,
                    "B_div": B_div,
                    "C_bad": C_bad,
                    "B_safe": B_safe,
                    "x0": t["x0"],
                    "phi_n": euler_phi(n),
                    "regime": "L=n" if L == n else "L>n",
                    "tight": int(B_safe == n - 1),
                }
            )

        lines.append(
            f"| {n} | {total} | {min_all} | {min_Ln} | {min_Lgt} | {tight} | {tight_Ln} | {tight_profile_mismatch} |"
        )

    # Include specific non-canonical example requested in prior discussion.
    ex_E = (1, 3, 4, 5)
    ex_n = 5
    ex = eval_case2_tuple(ex_E, ex_n)
    lines.append("")
    lines.append("## Non-canonical high-C_bad example")
    lines.append(
        f"For `n={ex_n}`, `E={ex_E}`: `L={ex['L']}`, `B_div={ex['B_div']}`, `C_bad={ex['C_bad']}`, `B_safe={ex['B_safe']}`, `x0={ex['x0']}`, `phi(5)={euler_phi(5)}`."
    )

    # Higher-n randomized stress for L=n class only.
    rng = random.Random(20260301)
    lines.append("")
    lines.append("## Random stress for anchor regime L=n (higher n)")
    lines.append("| n | tested tuples (L=n) | violations of (B_div=n-1, C_bad=0, B_safe=n-1) |")
    lines.append("|---:|---:|---:|")
    for n in [8, 9, 10, 11, 12, 14, 15, 16, 18, 20]:
        divisors = [d for d in range(1, n + 1) if n % d == 0]
        tested = 0
        violations = 0
        for _ in range(350):
            E = [rng.choice(divisors) for _ in range(n - 1)]
            if n not in E:
                E[rng.randrange(n - 1)] = n
            E = tuple(E)
            if math.gcd(*E) != 1:
                continue
            if math.lcm(*E) != n:
                continue
            tested += 1
            t = eval_case2_tuple(E, n)
            if not (t["B_div"] == n - 1 and t["C_bad"] == 0 and t["B_safe"] == n - 1):
                violations += 1
        lines.append(f"| {n} | {tested} | {violations} |")

    with open(OUT_ROWS, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    with open(OUT_SUMMARY, "w") as f:
        f.write("\n".join(lines) + "\n")

    print("Wrote:", OUT_ROWS)
    print("Wrote:", OUT_SUMMARY)


if __name__ == "__main__":
    main()
