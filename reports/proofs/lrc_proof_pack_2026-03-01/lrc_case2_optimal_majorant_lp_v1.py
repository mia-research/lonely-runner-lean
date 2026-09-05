#!/usr/bin/env python3
from __future__ import annotations

import csv
import itertools
import math
import random
from dataclasses import dataclass
from math import comb
from typing import List, Tuple

import numpy as np

OUT_COEFF = "/tmp/lrc_case2_optimal_majorant_coeffs_v1.csv"
OUT_RESULTS = "/tmp/lrc_case2_optimal_majorant_results_v1.csv"
OUT_SUMMARY = "/tmp/lrc_case2_optimal_majorant_summary_v1.md"

EXH_MAX_E_BY_N = {
    3: 12,
    4: 9,
    5: 7,
    6: 8,
}

RAND_CONFIGS = [
    (7, 11, 220),
    (8, 11, 160),
    (9, 12, 120),
    (10, 12, 90),
    (11, 12, 60),
    (12, 12, 45),
]


@dataclass
class LPResult:
    T: int
    m: int
    z: float
    coeffs: List[float]
    active: List[Tuple[str, int]]


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


def build_constraints(m: int, T: int):
    """
    Variables: v=[c1..cT, z].
    Constraints:
      (Aq) p(q) >= 1            -> -sum c_t C(q,t) <= -1
      (Bq) p(q)-1 <= z          -> sum c_t C(q,t) - z <= 1
      (Z)  z >= 0               -> -z <= 0
    """
    cons = []
    for q in range(1, m + 1):
        a = np.zeros(T + 1)
        for t in range(1, T + 1):
            a[t - 1] = -choose(q, t)
        cons.append((a, -1.0, ("A", q)))

    for q in range(1, m + 1):
        a = np.zeros(T + 1)
        for t in range(1, T + 1):
            a[t - 1] = choose(q, t)
        a[T] = -1.0
        cons.append((a, 1.0, ("B", q)))

    a = np.zeros(T + 1)
    a[T] = -1.0
    cons.append((a, 0.0, ("Z", 0)))
    return cons


def solve_lp_vertex_enum(m: int, T: int, tol: float = 1e-9) -> LPResult:
    cons = build_constraints(m, T)
    d = T + 1

    best_v = None
    best_z = float("inf")
    best_active = None

    for combo in itertools.combinations(range(len(cons)), d):
        Aeq = np.vstack([cons[i][0] for i in combo])
        beq = np.array([cons[i][1] for i in combo], dtype=float)

        try:
            v = np.linalg.solve(Aeq, beq)
        except np.linalg.LinAlgError:
            continue

        feasible = True
        for a, b, _tag in cons:
            if float(np.dot(a, v) - b) > tol:
                feasible = False
                break
        if not feasible:
            continue

        z = float(v[T])
        if z < -1e-7:
            continue

        if z < best_z - 1e-10:
            best_z = z
            best_v = v.copy()
            best_active = [cons[i][2] for i in combo]

    if best_v is None:
        raise RuntimeError(f"LP infeasible for m={m}, T={T}")

    coeffs = [float(best_v[t - 1]) for t in range(1, T + 1)]
    return LPResult(T=T, m=m, z=float(best_v[T]), coeffs=coeffs, active=best_active)


def eval_tuple_moments(E: Tuple[int, ...], n: int, T: int):
    L = math.lcm(*E)
    N = n * L
    lo = L
    hi = (n - 1) * L

    E_div = [e for e in E if e % n == 0]
    E_non = [e for e in E if e % n != 0]

    B_div = [b for b in range(L) if all(lo <= (e * b) % N <= hi for e in E_div)]

    M = [0.0] * (T + 1)
    x0 = 0
    B_safe = 0

    for b in B_div:
        q = []
        for a in range(n):
            k = a * L + b
            qq = 0
            for e in E_non:
                r = (e * k) % N
                if r < lo or r > hi:
                    qq += 1
            q.append(qq)

        cover = sum(1 for v in q if v > 0)
        if cover < n:
            B_safe += 1
            x0 += sum(1 for v in q if v == 0)
        else:
            for t in range(1, T + 1):
                M[t] += sum(choose(v, t) for v in q)

    rhs = float(n * (len(B_div) - (n - 1)))
    return {
        "L": L,
        "N": N,
        "B_div": len(B_div),
        "B_safe": B_safe,
        "x0": x0,
        "M": M,
        "rhs": rhs,
    }


def lhs_from_coeff(M: List[float], coeffs: List[float]) -> float:
    return sum(c * M[t] for t, c in enumerate(coeffs, start=1))


def fixed_g3_coeff(T: int) -> List[float]:
    c = [0.0] * T
    if T >= 1:
        c[0] = 1.0
    if T >= 2:
        c[1] = -1.0
    if T >= 3:
        c[2] = 1.0
    return c


def fixed_g5_coeff(T: int) -> List[float]:
    c = [0.0] * T
    if T >= 1:
        c[0] = 1.0
    if T >= 2:
        c[1] = -1.0
    if T >= 3:
        c[2] = 1.0
    if T >= 4:
        c[3] = -1.0
    if T >= 5:
        c[4] = 1.0
    return c


def main():
    coeff_rows = []
    result_rows = []

    lp_cache = {}
    for m in range(1, 11):
        for T in (1, 2, 3, 4, 5):
            if T > m:
                continue
            res = solve_lp_vertex_enum(m, T)
            lp_cache[(m, T)] = res
            coeff_rows.append({
                "m": m,
                "T": T,
                "z": res.z,
                "coeffs": " ".join(f"{x:.10g}" for x in res.coeffs),
                "active": ";".join(f"{k}{q}" for k, q in res.active),
            })

    def pick_lp_coeff(m: int, T_target: int):
        T_use = min(m, T_target)
        if T_use <= 0:
            return None
        return lp_cache[(m, T_use)].coeffs

    summary = []

    # Exhaustive n<=6
    for n, max_e in EXH_MAX_E_BY_N.items():
        phi_n = euler_phi(n)
        m = n - 2

        cand = {
            "g3": fixed_g3_coeff(5),
            "g5": fixed_g5_coeff(5),
            "lpT3": pick_lp_coeff(m, 3),
            "lpT5": pick_lp_coeff(m, 5),
        }

        tuples = 0
        ok_goal = 0
        ok = {k: 0 for k, v in cand.items() if v is not None}

        for E in itertools.product(range(1, max_e + 1), repeat=n - 1):
            if math.gcd(*E) != 1:
                continue
            if not any(e % n == 0 for e in E):
                continue

            tuples += 1
            t = eval_tuple_moments(E, n, T=5)
            if t["x0"] >= phi_n:
                ok_goal += 1

            lhs_vals = {}
            for name, coeff in cand.items():
                if coeff is None:
                    continue
                lhs_vals[name] = lhs_from_coeff(t["M"], coeff)
                if lhs_vals[name] <= t["rhs"] + 1e-9:
                    ok[name] += 1

            result_rows.append({
                "mode": "exh",
                "n": n,
                "e_tuple": " ".join(map(str, E)),
                "x0": t["x0"],
                "phi": phi_n,
                "rhs": t["rhs"],
                "lhs_g3": lhs_vals.get("g3", ""),
                "lhs_g5": lhs_vals.get("g5", ""),
                "lhs_lpT3": lhs_vals.get("lpT3", ""),
                "lhs_lpT5": lhs_vals.get("lpT5", ""),
            })

        summary.append({
            "mode": "exh",
            "n": n,
            "tuples": tuples,
            "goal": ok_goal,
            "ok": ok,
            "m": m,
            "zT3": lp_cache[(m, min(m, 3))].z,
            "zT5": lp_cache[(m, min(m, 5))].z,
        })

    # Random higher n
    rng = random.Random(20260301)
    for n, max_e, samples in RAND_CONFIGS:
        phi_n = euler_phi(n)
        m = n - 2
        if m > 10:
            continue

        cand = {
            "g3": fixed_g3_coeff(5),
            "g5": fixed_g5_coeff(5),
            "lpT3": pick_lp_coeff(m, 3),
            "lpT5": pick_lp_coeff(m, 5),
        }

        seen = 0
        ok_goal = 0
        ok = {k: 0 for k, v in cand.items() if v is not None}

        while seen < samples:
            E = tuple(rng.randint(1, max_e) for _ in range(n - 1))
            if math.gcd(*E) != 1:
                continue
            if not any(e % n == 0 for e in E):
                continue

            seen += 1
            t = eval_tuple_moments(E, n, T=5)
            if t["x0"] >= phi_n:
                ok_goal += 1

            lhs_vals = {}
            for name, coeff in cand.items():
                if coeff is None:
                    continue
                lhs_vals[name] = lhs_from_coeff(t["M"], coeff)
                if lhs_vals[name] <= t["rhs"] + 1e-9:
                    ok[name] += 1

            result_rows.append({
                "mode": "rand",
                "n": n,
                "e_tuple": " ".join(map(str, E)),
                "x0": t["x0"],
                "phi": phi_n,
                "rhs": t["rhs"],
                "lhs_g3": lhs_vals.get("g3", ""),
                "lhs_g5": lhs_vals.get("g5", ""),
                "lhs_lpT3": lhs_vals.get("lpT3", ""),
                "lhs_lpT5": lhs_vals.get("lpT5", ""),
            })

        summary.append({
            "mode": "rand",
            "n": n,
            "tuples": seen,
            "goal": ok_goal,
            "ok": ok,
            "m": m,
            "zT3": lp_cache[(m, min(m, 3))].z,
            "zT5": lp_cache[(m, min(m, 5))].z,
        })

    with open(OUT_COEFF, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=["m", "T", "z", "coeffs", "active"])
        w.writeheader()
        w.writerows(coeff_rows)

    with open(OUT_RESULTS, "w", newline="") as f:
        w = csv.DictWriter(
            f,
            fieldnames=["mode", "n", "e_tuple", "x0", "phi", "rhs", "lhs_g3", "lhs_g5", "lhs_lpT3", "lhs_lpT5"],
        )
        w.writeheader()
        w.writerows(result_rows)

    lines = []
    lines.append("# Case-2 Optimal Majorant LP/Dual Scan (v1)")
    lines.append("")
    lines.append("LP setup (vertex enumeration):")
    lines.append("- `p(q)=sum_{t=1..T} c_t C(q,t)` majorizes `1_{q>0}` on `q=1..m`.")
    lines.append("- constraints: `p(q)>=1`, `p(q)-1<=z`, `z>=0`; minimize `z`.")
    lines.append("")
    lines.append("## LP coefficients")
    lines.append("| m | T | z* | coeffs |")
    lines.append("|---:|---:|---:|---|")
    for r in coeff_rows:
        lines.append(f"| {r['m']} | {r['T']} | {float(r['z']):.6g} | `{r['coeffs']}` |")

    lines.append("")
    lines.append("## Forcing rates")
    lines.append("| mode | n | tuples | x0>=phi | g3 | g5 | lpT3 | lpT5 |")
    lines.append("|---|---:|---:|---:|---:|---:|---:|---:|")
    for s in summary:
        t = s["tuples"]
        ok = s["ok"]
        lines.append(
            f"| {s['mode']} | {s['n']} | {t} | {s['goal']}/{t} | "
            f"{ok.get('g3',0)}/{t} | {ok.get('g5',0)}/{t} | {ok.get('lpT3',0)}/{t} | {ok.get('lpT5',0)}/{t} |"
        )

    lines.append("")
    lines.append("Artifacts:")
    lines.append(f"- coeffs: `{OUT_COEFF}`")
    lines.append(f"- results: `{OUT_RESULTS}`")
    lines.append(f"- summary: `{OUT_SUMMARY}`")

    with open(OUT_SUMMARY, "w") as f:
        f.write("\n".join(lines) + "\n")

    print("Wrote:", OUT_COEFF)
    print("Wrote:", OUT_RESULTS)
    print("Wrote:", OUT_SUMMARY)


if __name__ == "__main__":
    main()
