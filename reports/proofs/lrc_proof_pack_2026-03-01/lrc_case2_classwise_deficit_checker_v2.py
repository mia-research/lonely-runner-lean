#!/usr/bin/env python3
from __future__ import annotations

import csv
import math
import random
from itertools import product
from math import comb

OUT_ROWS = "/tmp/lrc_case2_classwise_deficit_rows_v2.csv"
OUT_SUMMARY = "/tmp/lrc_case2_classwise_deficit_summary_v2.md"

EXH_MAX = {
    3: 12,
    4: 9,
    5: 7,
    6: 8,
}

RND_CFG = [
    (7, 12, 2000),
    (8, 12, 1600),
    (9, 12, 1200),
    (10, 12, 900),
    (11, 12, 700),
    (12, 12, 500),
]

L_CAP = 2500


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


def choose(q: int, t: int) -> int:
    if q < t:
        return 0
    return comb(q, t)


def odd_bonf_ub(q_branch: list[int], k_odd: int) -> int:
    total = 0
    for t in range(1, k_odd + 1):
        vt = 0
        for q in q_branch:
            vt += choose(q, t)
        total += vt if (t % 2 == 1) else -vt
    return total


def tuple_classes(E: tuple[int, ...], n: int):
    L = math.lcm(*E)
    N = n * L
    lo = L
    hi = (n - 1) * L

    E_div = [e for e in E if e % n == 0]
    E_non = [e for e in E if e % n != 0]

    B_div = [b for b in range(L) if all(lo <= (e * b) % N <= hi for e in E_div)]

    classes = {}
    k_n = (n - 1) if ((n - 1) % 2 == 1) else (n - 2)

    for b in B_div:
        sig = []
        cap = 0
        solv = 0
        speed_branches: list[tuple[int, list[int]]] = []

        for e in E_non:
            x = (e * b) % N
            u = x // L
            d = 1 if (x % L) > 0 else 0
            g = math.gcd(e, n)

            cap += (1 + d) * g
            sig.append((e, u, d))

            branches = []
            c0 = (-u) % n
            if c0 % g == 0:
                branches.append(c0)
            if d:
                c1 = (-u - 1) % n
                if c1 % g == 0:
                    branches.append(c1)

            solv += len(branches) * g
            speed_branches.append((e, branches))

        q_speed = [0] * n
        q_branch = [0] * n

        for e, branches in speed_branches:
            speed_hit = [False] * n
            for c in branches:
                for a in range(n):
                    if (e * a - c) % n == 0:
                        q_branch[a] += 1
                        speed_hit[a] = True
            for a in range(n):
                if speed_hit[a]:
                    q_speed[a] += 1

        cover = sum(1 for q in q_speed if q > 0)
        delta = n - cover

        V1 = sum(q_branch)
        V2 = sum(choose(q, 2) for q in q_branch)
        V3 = sum(choose(q, 3) for q in q_branch)
        V4 = sum(choose(q, 4) for q in q_branch)
        V5 = sum(choose(q, 5) for q in q_branch)

        UB3 = V1 - V2 + V3
        UB5 = UB3 - V4 + V5
        UBN = odd_bonf_ub(q_branch, k_n)

        key = (tuple(sig), cover, delta, cap, solv, UB3, UB5, UBN)
        classes[key] = classes.get(key, 0) + 1

    return classes


CANDIDATES = {
    "ub3": lambda n, cap, solv, ub3, ub5, ubn: min(n, ub3),
    "ub5": lambda n, cap, solv, ub3, ub5, ubn: min(n, ub5),
    "ubN": lambda n, cap, solv, ub3, ub5, ubn: min(n, ubn),
    "min_bN_cap": lambda n, cap, solv, ub3, ub5, ubn: min(n, ubn, cap),
    "min_bN_capsolv": lambda n, cap, solv, ub3, ub5, ubn: min(n, ubn, cap, solv),
    "min_all": lambda n, cap, solv, ub3, ub5, ubn: min(n, ub3, ub5, ubn, cap, solv),
}


def eval_tuple(E: tuple[int, ...], n: int):
    classes = tuple_classes(E, n)
    x0 = 0
    lb = {k: 0 for k in CANDIDATES}

    for (_sig, _cover, delta, cap, solv, ub3, ub5, ubn), Ns in classes.items():
        x0 += Ns * delta
        for k, fn in CANDIDATES.items():
            U = fn(n, cap, solv, ub3, ub5, ubn)
            lb[k] += Ns * max(0, n - U)

    return x0, lb


def init_stats():
    return {
        k: {
            "viol_nminus1": 0,
            "viol_phi": 0,
            "min_lb": None,
            "min_gap": None,
            "first_fail": None,
        }
        for k in CANDIDATES
    }


def upd_stats(stats, k, n, phi_n, E, L, x0, lbv):
    st = stats[k]
    if lbv < n - 1:
        st["viol_nminus1"] += 1
        if st["first_fail"] is None:
            st["first_fail"] = (E, L, x0, lbv)
    if lbv < phi_n:
        st["viol_phi"] += 1
    if st["min_lb"] is None or lbv < st["min_lb"]:
        st["min_lb"] = lbv
    g = x0 - lbv
    if st["min_gap"] is None or g < st["min_gap"]:
        st["min_gap"] = g


def main() -> None:
    random.seed(0)
    rows = []
    lines = []

    lines.append("# Case-2 Classwise Deficit Checker (v2)")
    lines.append("")
    lines.append("Tested classwise lower bounds:")
    lines.append("`x0 >= Σ_s N_s * max(0, n-U_s)` with CRT-derived `U_s`.")
    lines.append("")

    # Exhaustive n=3..6
    lines.append("## Exhaustive n=3..6")
    lines.append("| n | tuples | candidate | viol(lb>=n-1) | viol(lb>=phi) | min lb | min (x0-lb) |")
    lines.append("|---:|---:|---|---:|---:|---:|---:|")

    for n, max_e in EXH_MAX.items():
        phi_n = euler_phi(n)
        stats = init_stats()
        tuples = 0

        for E in product(range(1, max_e + 1), repeat=n - 1):
            if math.gcd(*E) != 1:
                continue
            if not any(e % n == 0 for e in E):
                continue
            tuples += 1

            L = math.lcm(*E)
            x0, lb = eval_tuple(E, n)

            rec = {
                "mode": "exhaustive",
                "n": n,
                "phi_n": phi_n,
                "e_tuple": " ".join(map(str, E)),
                "L": L,
                "x0": x0,
            }
            for k in CANDIDATES:
                rec[f"lb_{k}"] = lb[k]
                rec[f"gap_{k}"] = x0 - lb[k]
                upd_stats(stats, k, n, phi_n, E, L, x0, lb[k])
            rows.append(rec)

        for k in CANDIDATES:
            st = stats[k]
            lines.append(
                f"| {n} | {tuples} | `{k}` | {st['viol_nminus1']} | {st['viol_phi']} | {st['min_lb']} | {st['min_gap']} |"
            )

    # Random n=7..12
    lines.append("")
    lines.append(f"## Random n=7..12 (L<={L_CAP})")
    lines.append("| n | kept tuples | candidate | viol(lb>=n-1) | viol(lb>=phi) | min lb | min (x0-lb) |")
    lines.append("|---:|---:|---|---:|---:|---:|---:|")

    for n, max_e, keep in RND_CFG:
        phi_n = euler_phi(n)
        stats = init_stats()
        kept = 0
        tries = 0

        while kept < keep and tries < keep * 200:
            tries += 1
            E = tuple(random.randint(1, max_e) for _ in range(n - 1))
            if math.gcd(*E) != 1:
                continue
            if not any(e % n == 0 for e in E):
                continue
            L = math.lcm(*E)
            if L > L_CAP:
                continue

            x0, lb = eval_tuple(E, n)
            kept += 1

            rec = {
                "mode": "random",
                "n": n,
                "phi_n": phi_n,
                "e_tuple": " ".join(map(str, E)),
                "L": L,
                "x0": x0,
            }
            for k in CANDIDATES:
                rec[f"lb_{k}"] = lb[k]
                rec[f"gap_{k}"] = x0 - lb[k]
                upd_stats(stats, k, n, phi_n, E, L, x0, lb[k])
            rows.append(rec)

        for k in CANDIDATES:
            st = stats[k]
            lines.append(
                f"| {n} | {kept} | `{k}` | {st['viol_nminus1']} | {st['viol_phi']} | {st['min_lb']} | {st['min_gap']} |"
            )

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
