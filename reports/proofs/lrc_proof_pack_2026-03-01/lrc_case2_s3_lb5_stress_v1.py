#!/usr/bin/env python3
from __future__ import annotations

import csv
import math
import random
from math import comb

OUT_ROWS = "/tmp/lrc_case2_s3_lb5_stress_rows_v1.csv"
OUT_SUMMARY = "/tmp/lrc_case2_s3_lb5_stress_summary_v1.md"

CFG = [
    (13, 14, 160, 1200),
    (14, 14, 140, 1200),
    (15, 15, 120, 1800),
]


def choose(q: int, t: int) -> int:
    return comb(q, t) if q >= t else 0


def eval_lb5(E: tuple[int, ...], n: int):
    L = math.lcm(*E)
    N = n * L
    lo = L
    hi = (n - 1) * L

    E_div = [e for e in E if e % n == 0]
    E_non = [e for e in E if e % n != 0]

    B = [b for b in range(L) if all(lo <= (e * b) % N <= hi for e in E_div)]

    classes = {}

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

        V1 = sum(q_branch)
        V2 = sum(choose(q, 2) for q in q_branch)
        V3 = sum(choose(q, 3) for q in q_branch)
        V4 = sum(choose(q, 4) for q in q_branch)
        V5 = sum(choose(q, 5) for q in q_branch)
        UB5 = V1 - V2 + V3 - V4 + V5

        sig = (cover, UB5)
        classes[sig] = classes.get(sig, 0) + 1

    x0 = sum(Ns * (n - cover) for (cover, _UB5), Ns in classes.items())
    lb5 = sum(Ns * max(0, n - min(n, UB5)) for (_cover, UB5), Ns in classes.items())

    return L, len(B), x0, lb5


def main() -> None:
    random.seed(0)

    rows = []
    lines = []

    lines.append("# S3 LB5 Stress (v1)")
    lines.append("")
    lines.append("Checks candidate structural lower bound:")
    lines.append("- `LB5(E) = sum_s N_s * max(0, n-UB5_s) >= n-1`.")
    lines.append("")
    lines.append("| n | kept tuples | violations LB5<n-1 | min LB5 | min x0 |")
    lines.append("|---:|---:|---:|---:|---:|")

    for n, max_e, keep_target, L_cap in CFG:
        kept = 0
        tries = 0
        viol = 0
        min_lb5 = None
        min_x0 = None
        ex = None

        while kept < keep_target and tries < keep_target * 600:
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
            L, B_div, x0, lb5 = eval_lb5(E, n)

            if lb5 < (n - 1):
                viol += 1
                if ex is None:
                    ex = (E, L, B_div, x0, lb5)

            if min_lb5 is None or lb5 < min_lb5:
                min_lb5 = lb5
            if min_x0 is None or x0 < min_x0:
                min_x0 = x0

            rows.append(
                {
                    "n": n,
                    "e_tuple": " ".join(map(str, E)),
                    "L": L,
                    "B_div": B_div,
                    "x0": x0,
                    "lb5": lb5,
                    "lb5_minus_nminus1": lb5 - (n - 1),
                }
            )

        lines.append(f"| {n} | {kept} | {viol} | {min_lb5} | {min_x0} |")
        if ex:
            lines.append(f"- first violation n={n}: `E={ex[0]}`, `L={ex[1]}`, `B_div={ex[2]}`, `x0={ex[3]}`, `LB5={ex[4]}`")

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
