#!/usr/bin/env python3
from __future__ import annotations

import csv
import math
import random
from math import comb

OUT_ROWS = "/tmp/lrc_case2_s3_order_ladder_rows_v1.csv"
OUT_SUMMARY = "/tmp/lrc_case2_s3_order_ladder_summary_v1.md"

CFG = [
    (7, 12, 600, 1200),
    (8, 12, 500, 1200),
    (9, 12, 400, 1200),
    (10, 12, 300, 1200),
    (11, 12, 220, 1800),
    (12, 12, 180, 1800),
    (13, 14, 180, 1800),
    (14, 14, 140, 1800),
    (15, 15, 100, 2400),
]


def choose(q: int, t: int) -> int:
    return comb(q, t) if q >= t else 0


def odd_ub(q_branch: list[int], k: int) -> int:
    s = 0
    for t in range(1, k + 1):
        vt = sum(choose(q, t) for q in q_branch)
        s += vt if (t % 2 == 1) else -vt
    return s


def eval_lb_k(E: tuple[int, ...], n: int, k: int):
    L = math.lcm(*E)
    N = n * L
    lo = L
    hi = (n - 1) * L

    E_div = [e for e in E if e % n == 0]
    E_non = [e for e in E if e % n != 0]

    B = [b for b in range(L) if all(lo <= (e * b) % N <= hi for e in E_div)]

    x0 = 0
    lb = 0

    for b in B:
        speed_branches = []
        for e in E_non:
            x = (e * b) % N
            u = x // L
            d = 1 if (x % L) else 0
            g = math.gcd(e, n)

            arr = []
            c0 = (-u) % n
            if c0 % g == 0:
                arr.append(c0)
            if d:
                c1 = (-u - 1) % n
                if c1 % g == 0:
                    arr.append(c1)
            speed_branches.append((e, arr))

        q_speed = [0] * n
        q_branch = [0] * n

        for e, arr in speed_branches:
            hit = [False] * n
            for c in arr:
                for a in range(n):
                    if (e * a - c) % n == 0:
                        q_branch[a] += 1
                        hit[a] = True
            for a in range(n):
                if hit[a]:
                    q_speed[a] += 1

        cover = sum(1 for q in q_speed if q > 0)
        x0 += n - cover

        ubk = odd_ub(q_branch, k)
        lb += max(0, n - min(n, ubk))

    return L, len(B), x0, lb


def main() -> None:
    random.seed(3)

    rows = []
    lines = []

    lines.append("# S3 Order Ladder Stress (v1)")
    lines.append("")
    lines.append("Compares odd-order classwise deficit bounds LB5 vs LB7:")
    lines.append("- `LBk(E) = sum_s N_s * max(0, n-UBk_s)`")
    lines.append("")
    lines.append("| n | kept | viol(LB5<n-1) | viol(LB7<n-1) | min LB5 | min LB7 |")
    lines.append("|---:|---:|---:|---:|---:|---:|")

    for n, max_e, keep_target, L_cap in CFG:
        kept = 0
        tries = 0
        viol5 = 0
        viol7 = 0
        min5 = None
        min7 = None
        ex5 = None

        while kept < keep_target and tries < keep_target * 700:
            tries += 1
            E = tuple(random.randint(1, max_e) for _ in range(n - 1))
            if math.gcd(*E) != 1:
                continue
            if not any(e % n == 0 for e in E):
                continue

            L = math.lcm(*E)
            if L > L_cap:
                continue

            kept += 1
            L, B_div, x0, lb5 = eval_lb_k(E, n, 5)
            _, _, _, lb7 = eval_lb_k(E, n, 7)

            if lb5 < (n - 1):
                viol5 += 1
                if ex5 is None:
                    ex5 = (E, L, B_div, x0, lb5)
            if lb7 < (n - 1):
                viol7 += 1

            min5 = lb5 if min5 is None or lb5 < min5 else min5
            min7 = lb7 if min7 is None or lb7 < min7 else min7

            rows.append(
                {
                    "n": n,
                    "e_tuple": " ".join(map(str, E)),
                    "L": L,
                    "B_div": B_div,
                    "x0": x0,
                    "lb5": lb5,
                    "lb7": lb7,
                    "lb5_minus_nminus1": lb5 - (n - 1),
                    "lb7_minus_nminus1": lb7 - (n - 1),
                }
            )

        lines.append(f"| {n} | {kept} | {viol5} | {viol7} | {min5} | {min7} |")
        if ex5:
            lines.append(f"- first LB5 violation n={n}: `E={ex5[0]}`, `L={ex5[1]}`, `B_div={ex5[2]}`, `x0={ex5[3]}`, `LB5={ex5[4]}`")

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
