#!/usr/bin/env python3
from __future__ import annotations

import csv
import math
from itertools import product

OUT_TABLE = "/Users/trentpalelei/Desktop/Math Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_factorization_rows_v1.csv"
OUT_SUMMARY = "/Users/trentpalelei/Desktop/Math Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_factorization_summary_v1.md"

# bounded exhaustive ranges where case-2 appears in existing grids
MAX_E_BY_N = {
    3: 12,
    4: 9,
    5: 7,
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


def analyze_tuple(E: tuple[int, ...], n: int):
    L = math.lcm(*E)
    N = n * L
    lo = L
    hi = (n - 1) * L

    E_div = tuple(e for e in E if e % n == 0)
    E_non = tuple(e for e in E if e % n != 0)

    # B_div = b-values satisfying all divisible-speed constraints
    B_div = []
    A_counts = []

    for b in range(L):
        ok_div = True
        for e in E_div:
            r = (e * b) % N  # independent of a
            if not (lo <= r <= hi):
                ok_div = False
                break
        if not ok_div:
            continue

        B_div.append(b)

        # A_b = number of a in {0,...,n-1} safe under non-div constraints
        good_a = 0
        for a in range(n):
            k = a * L + b
            ok_non = True
            for e in E_non:
                r = (e * k) % N
                if not (lo <= r <= hi):
                    ok_non = False
                    break
            if ok_non:
                good_a += 1
        A_counts.append(good_a)

    x0 = sum(A_counts)

    # cross-check against direct definition
    x0_direct = 0
    for k in range(N):
        ok = True
        for e in E:
            r = (e * k) % N
            if not (lo <= r <= hi):
                ok = False
                break
        if ok:
            x0_direct += 1

    assert x0 == x0_direct, (E, n, x0, x0_direct)

    return {
        "L": L,
        "N": N,
        "x0": x0,
        "B_div_size": len(B_div),
        "A_min": min(A_counts) if A_counts else 0,
        "A_max": max(A_counts) if A_counts else 0,
        "A_sum": x0,
        "E_div": " ".join(map(str, E_div)),
        "E_non": " ".join(map(str, E_non)),
    }


def main() -> None:
    rows = []
    summary = []

    for n, max_e in MAX_E_BY_N.items():
        ph = euler_phi(n)

        tuples_case2 = 0
        min_x0 = None
        min_B = None
        min_Amax = None
        min_ratio = None

        min_x0_examples = []
        min_B_examples = []

        for E in product(range(1, max_e + 1), repeat=n - 1):
            if math.gcd(*E) != 1:
                continue
            if not any(e % n == 0 for e in E):
                continue

            tuples_case2 += 1
            r = analyze_tuple(E, n)

            ratio = r["x0"] / ph

            if min_x0 is None or r["x0"] < min_x0:
                min_x0 = r["x0"]
                min_x0_examples = [E]
            elif r["x0"] == min_x0 and len(min_x0_examples) < 8:
                min_x0_examples.append(E)

            if min_B is None or r["B_div_size"] < min_B:
                min_B = r["B_div_size"]
                min_B_examples = [E]
            elif r["B_div_size"] == min_B and len(min_B_examples) < 8:
                min_B_examples.append(E)

            if min_Amax is None or r["A_max"] < min_Amax:
                min_Amax = r["A_max"]

            if min_ratio is None or ratio < min_ratio:
                min_ratio = ratio

            rows.append(
                {
                    "n": n,
                    "phi_n": ph,
                    "e_tuple": " ".join(map(str, E)),
                    **r,
                    "x0_over_phi": f"{ratio:.6f}",
                }
            )

        summary.append(
            {
                "n": n,
                "phi_n": ph,
                "case2_tuples": tuples_case2,
                "min_x0": min_x0,
                "min_x0_over_phi": min_ratio,
                "min_B_div_size": min_B,
                "min_A_max": min_Amax,
                "min_x0_examples": ["(" + ",".join(map(str, e)) + ")" for e in min_x0_examples],
                "min_B_examples": ["(" + ",".join(map(str, e)) + ")" for e in min_B_examples],
            }
        )

    # write rows
    with open(OUT_TABLE, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    # write summary
    lines = []
    lines.append("# Lemma E Case-2 Factorization Scan (v1)")
    lines.append("")
    lines.append("Decomposition used per tuple:")
    lines.append("- `x0 = sum_{b in B_div} |A_b|`")
    lines.append("- `B_div`: b-values surviving all divisible-speed constraints")
    lines.append("- `A_b`: number of a in {0,...,n-1} surviving all non-divisible constraints at k=aL+b")
    lines.append("")
    lines.append("| n | phi(n) | case2 tuples | min x0 | min x0/phi | min |B_div| | min max_b |A_b| |")
    lines.append("|---:|---:|---:|---:|---:|---:|---:|")
    for s in summary:
        lines.append(
            f"| {s['n']} | {s['phi_n']} | {s['case2_tuples']} | {s['min_x0']} | {s['min_x0_over_phi']:.3f} | {s['min_B_div_size']} | {s['min_A_max']} |"
        )

    lines.append("")
    lines.append("## Min-x0 examples")
    for s in summary:
        lines.append(f"- n={s['n']}: {', '.join(s['min_x0_examples'])}")

    lines.append("")
    lines.append("## Min-|B_div| examples")
    for s in summary:
        lines.append(f"- n={s['n']}: {', '.join(s['min_B_examples'])}")

    lines.append("")
    lines.append("Artifacts:")
    lines.append(f"- rows: `{OUT_TABLE}`")
    lines.append(f"- summary: `{OUT_SUMMARY}`")

    with open(OUT_SUMMARY, "w") as f:
        f.write("\n".join(lines) + "\n")

    print("FINAL")
    print("rows", OUT_TABLE)
    print("summary", OUT_SUMMARY)


if __name__ == "__main__":
    main()
