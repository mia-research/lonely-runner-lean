#!/usr/bin/env python3
from __future__ import annotations

import csv
import math
from itertools import product

OUT_TABLE = "/Users/trentpalelei/Desktop/Math Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_bsafe_rows_v1.csv"
OUT_SUMMARY = "/Users/trentpalelei/Desktop/Math Ex/reports/proofs/lrc_proof_pack_2026-03-01/lrc_case2_bsafe_summary_v1.md"

# chosen to include case-2 tuples (i.e. allow multiples of n)
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


def analyze_case2(E: tuple[int, ...], n: int):
    L = math.lcm(*E)
    N = n * L
    lo = L
    hi = (n - 1) * L

    E_div = tuple(e for e in E if e % n == 0)
    E_non = tuple(e for e in E if e % n != 0)

    B_div = 0
    B_safe = 0
    x0 = 0

    for b in range(L):
        # divisible-speed gate
        ok_div = True
        for e in E_div:
            r = (e * b) % N
            if not (lo <= r <= hi):
                ok_div = False
                break
        if not ok_div:
            continue

        B_div += 1

        # a-fiber count for this b
        a_count = 0
        for a in range(n):
            k = a * L + b
            ok_non = True
            for e in E_non:
                r = (e * k) % N
                if not (lo <= r <= hi):
                    ok_non = False
                    break
            if ok_non:
                a_count += 1

        if a_count > 0:
            B_safe += 1
        x0 += a_count

    return L, N, B_div, B_safe, x0


def main() -> None:
    rows = []
    summary = []

    for n, max_e in MAX_E_BY_N.items():
        ph = euler_phi(n)
        case2_tuples = 0

        min_Bsafe = None
        min_x0 = None
        min_Bdiv = None

        ex_Bsafe = []
        ex_x0 = []

        viol_Bsafe_ge_n1 = 0
        viol_Bsafe_ge_phi = 0
        viol_x0_ge_phi = 0

        for E in product(range(1, max_e + 1), repeat=n - 1):
            if math.gcd(*E) != 1:
                continue
            if not any(e % n == 0 for e in E):
                continue

            case2_tuples += 1
            L, N, B_div, B_safe, x0 = analyze_case2(E, n)

            if B_safe < n - 1:
                viol_Bsafe_ge_n1 += 1
            if B_safe < ph:
                viol_Bsafe_ge_phi += 1
            if x0 < ph:
                viol_x0_ge_phi += 1

            if min_Bsafe is None or B_safe < min_Bsafe:
                min_Bsafe = B_safe
                ex_Bsafe = [(E, L, B_div, B_safe, x0)]
            elif B_safe == min_Bsafe and len(ex_Bsafe) < 8:
                ex_Bsafe.append((E, L, B_div, B_safe, x0))

            if min_x0 is None or x0 < min_x0:
                min_x0 = x0
                ex_x0 = [(E, L, B_div, B_safe, x0)]
            elif x0 == min_x0 and len(ex_x0) < 8:
                ex_x0.append((E, L, B_div, B_safe, x0))

            if min_Bdiv is None or B_div < min_Bdiv:
                min_Bdiv = B_div

            rows.append(
                {
                    "n": n,
                    "phi_n": ph,
                    "e_tuple": " ".join(map(str, E)),
                    "L": L,
                    "N": N,
                    "B_div": B_div,
                    "B_safe": B_safe,
                    "x0": x0,
                    "Bsafe_over_phi": f"{B_safe / ph:.6f}",
                    "x0_over_phi": f"{x0 / ph:.6f}",
                }
            )

        summary.append(
            {
                "n": n,
                "phi": ph,
                "case2_tuples": case2_tuples,
                "min_Bdiv": min_Bdiv,
                "min_Bsafe": min_Bsafe,
                "min_x0": min_x0,
                "viol_Bsafe_ge_n1": viol_Bsafe_ge_n1,
                "viol_Bsafe_ge_phi": viol_Bsafe_ge_phi,
                "viol_x0_ge_phi": viol_x0_ge_phi,
                "ex_Bsafe": ex_Bsafe,
                "ex_x0": ex_x0,
            }
        )

    # write table
    with open(OUT_TABLE, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    # write summary
    lines = []
    lines.append("# Lemma E Case-2 B_safe Scan (v1)")
    lines.append("")
    lines.append("Definitions:")
    lines.append("- `B_div = {b : b passes all divisible-speed constraints}`")
    lines.append("- `B_safe = {b in B_div : exists a with k=aL+b safe for non-divisible constraints}`")
    lines.append("- `x0 = sum_{b in B_div} |A_b|`, so `x0 >= |B_safe|`.")
    lines.append("")
    lines.append("| n | phi(n) | case2 tuples | min B_div | min B_safe | min x0 | viol(B_safe>=n-1) | viol(B_safe>=phi) | viol(x0>=phi) |")
    lines.append("|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    for s in summary:
        lines.append(
            f"| {s['n']} | {s['phi']} | {s['case2_tuples']} | {s['min_Bdiv']} | {s['min_Bsafe']} | {s['min_x0']} | "
            f"{s['viol_Bsafe_ge_n1']} | {s['viol_Bsafe_ge_phi']} | {s['viol_x0_ge_phi']} |"
        )

    lines.append("")
    lines.append("## Min-B_safe examples")
    for s in summary:
        ex = ", ".join([f"{e} (L={L}, B_div={Bd}, B_safe={Bs}, x0={x0})" for e, L, Bd, Bs, x0 in s["ex_Bsafe"]])
        lines.append(f"- n={s['n']}: {ex}")

    lines.append("")
    lines.append("## Min-x0 examples")
    for s in summary:
        ex = ", ".join([f"{e} (L={L}, B_div={Bd}, B_safe={Bs}, x0={x0})" for e, L, Bd, Bs, x0 in s["ex_x0"]])
        lines.append(f"- n={s['n']}: {ex}")

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
