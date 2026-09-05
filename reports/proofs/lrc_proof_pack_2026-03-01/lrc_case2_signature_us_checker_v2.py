#!/usr/bin/env python3
from __future__ import annotations

import csv
import math
import random
from itertools import product
from math import comb

OUT_ROWS = "/tmp/lrc_case2_signature_us_rows_v2.csv"
OUT_SUMMARY = "/tmp/lrc_case2_signature_us_summary_v2.md"

# Exhaustive ranges used in previous Case-2 scans.
MAX_E_BY_N = {
    3: 12,
    4: 9,
    5: 7,
    6: 8,
}

# Additional random stress settings for higher n.
RANDOM_CONFIGS = [
    (7, 11, 300),
    (8, 11, 200),
    (9, 12, 140),
    (10, 12, 90),
]


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


def choose2(q: int) -> int:
    return q * (q - 1) // 2


def choose3(q: int) -> int:
    return q * (q - 1) * (q - 2) // 6


def choose4(q: int) -> int:
    return q * (q - 1) * (q - 2) * (q - 3) // 24


def choose5(q: int) -> int:
    return q * (q - 1) * (q - 2) * (q - 3) * (q - 4) // 120


def odd_bonf_ub(q_branch: list[int], k_odd: int) -> int:
    """UB_k = sum_{t=1..k odd} (-1)^{t+1} V_t, with V_t=sum_a C(q(a),t)."""
    total = 0
    for t in range(1, k_odd + 1):
        vt = 0
        for q in q_branch:
            if q >= t:
                vt += comb(q, t)
        total += vt if (t % 2 == 1) else -vt
    return total


def tuple_signature_data(E: tuple[int, ...], n: int):
    L = math.lcm(*E)
    N = n * L
    lo = L
    hi = (n - 1) * L

    E_div = [e for e in E if e % n == 0]
    E_non = [e for e in E if e % n != 0]

    B_div = [b for b in range(L) if all(lo <= (e * b) % N <= hi for e in E_div)]

    classes: dict[tuple, dict] = {}

    x0 = 0
    B_safe = 0

    # Dynamic odd truncation order candidate: largest odd <= n-1.
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
        bad = cover == n

        if not bad:
            B_safe += 1
            x0 += sum(1 for q in q_speed if q == 0)

        I = sum(q_speed)
        P = sum(choose2(q) for q in q_speed)
        T = sum(choose3(q) for q in q_speed)
        F = I - P + T

        V1 = sum(q_branch)
        V2 = sum(choose2(q) for q in q_branch)
        V3 = sum(choose3(q) for q in q_branch)
        V4 = sum(choose4(q) for q in q_branch)
        V5 = sum(choose5(q) for q in q_branch)

        UB3 = V1 - V2 + V3
        UB5 = UB3 - V4 + V5
        UBN = odd_bonf_ub(q_branch, k_n)

        sig_t = tuple(sig)
        row = classes.get(sig_t)
        if row is None:
            classes[sig_t] = {
                "N_s": 1,
                "bad": bad,
                "cover": cover,
                "I": I,
                "P": P,
                "T": T,
                "F": F,
                "cap": cap,
                "solv": solv,
                "UB3": UB3,
                "UB5": UB5,
                "UBN": UBN,
            }
        else:
            assert row["bad"] == bad
            assert row["cover"] == cover
            assert row["I"] == I
            assert row["P"] == P
            assert row["T"] == T
            assert row["F"] == F
            assert row["cap"] == cap
            assert row["solv"] == solv
            assert row["UB3"] == UB3
            assert row["UB5"] == UB5
            assert row["UBN"] == UBN
            row["N_s"] += 1

    x0_check = sum((0 if c["bad"] else c["N_s"] * (n - c["cover"])) for c in classes.values())
    assert x0_check == x0

    return {
        "L": L,
        "N": N,
        "B_div": len(B_div),
        "B_safe": B_safe,
        "x0": x0,
        "classes": classes,
        "k_n": k_n,
    }


def evaluate_tuple_bounds(n: int, phi_n: int, E: tuple[int, ...]):
    t = tuple_signature_data(E, n)
    B_div = t["B_div"]
    target = n * (B_div - (n - 1))

    bound_keys = ["cap", "solv", "b3", "b5", "bN", "hyb5", "hybN", "cov"]
    lhs = {k: 0 for k in bound_keys}
    class_diag = {k: {"pred": 0, "fp": 0, "fn": 0} for k in bound_keys}

    for sig, c in t["classes"].items():
        N_s = c["N_s"]
        F = c["F"]
        bad = c["bad"]

        cond_cap = c["cap"] >= n
        cond_solv = c["solv"] >= n
        cond_b3 = c["UB3"] >= n
        cond_b5 = c["UB5"] >= n
        cond_bN = c["UBN"] >= n
        cond_cov = c["cover"] == n

        U = {
            "cap": N_s if cond_cap else 0,
            "solv": N_s if cond_solv else 0,
            "b3": N_s if cond_b3 else 0,
            "b5": N_s if cond_b5 else 0,
            "bN": N_s if cond_bN else 0,
            "hyb5": N_s if (cond_cap and cond_solv and cond_b5) else 0,
            "hybN": N_s if (cond_cap and cond_solv and cond_bN) else 0,
            "cov": N_s if cond_cov else 0,
        }

        for k in bound_keys:
            lhs[k] += U[k] * F
            if U[k] > 0:
                class_diag[k]["pred"] += 1
            if U[k] > 0 and not bad:
                class_diag[k]["fp"] += 1
            if bad and U[k] == 0:
                class_diag[k]["fn"] += 1

    ok = {k: (lhs[k] <= target) for k in bound_keys}

    return {
        "tuple_data": t,
        "target": target,
        "ok": ok,
        "class_diag": class_diag,
        "lhs": lhs,
    }


def main() -> None:
    rows = []
    summary_exh = []

    bound_keys = ["cap", "solv", "b3", "b5", "bN", "hyb5", "hybN", "cov"]

    # Exhaustive block (n=3..6 grids).
    for n, max_e in MAX_E_BY_N.items():
        phi_n = euler_phi(n)

        tuples = 0
        ok_goal = 0
        ok_bound = {k: 0 for k in bound_keys}

        class_total = 0
        class_bad = 0
        class_diag_tot = {k: {"pred": 0, "fp": 0, "fn": 0} for k in bound_keys}

        for E in product(range(1, max_e + 1), repeat=n - 1):
            if math.gcd(*E) != 1:
                continue
            if not any(e % n == 0 for e in E):
                continue

            tuples += 1
            out = evaluate_tuple_bounds(n, phi_n, E)
            t = out["tuple_data"]

            if t["x0"] >= phi_n:
                ok_goal += 1
            for k in bound_keys:
                if out["ok"][k]:
                    ok_bound[k] += 1

            classes = t["classes"]
            for sig, c in classes.items():
                class_total += 1
                if c["bad"]:
                    class_bad += 1

                for k in bound_keys:
                    class_diag_tot[k]["pred"] += out["class_diag"][k]["pred"]
                    class_diag_tot[k]["fp"] += out["class_diag"][k]["fp"]
                    class_diag_tot[k]["fn"] += out["class_diag"][k]["fn"]

                rows.append({
                    "n": n,
                    "phi_n": phi_n,
                    "k_n": t["k_n"],
                    "e_tuple": " ".join(map(str, E)),
                    "L": t["L"],
                    "B_div": t["B_div"],
                    "N_s": c["N_s"],
                    "F_s": c["F"],
                    "cover_s": c["cover"],
                    "cap_s": c["cap"],
                    "solv_s": c["solv"],
                    "UB3_s": c["UB3"],
                    "UB5_s": c["UB5"],
                    "UBN_s": c["UBN"],
                    "bad_exact": int(c["bad"]),
                })

        # class_diag_tot above over-counts due per-class repeated whole tuple totals;
        # recompute properly from rows would be heavy. Keep tuple-level forcing as primary metric.
        summary_exh.append({
            "n": n,
            "phi": phi_n,
            "tuples": tuples,
            "ok_goal": ok_goal,
            "ok_bound": ok_bound,
            "class_total": class_total,
            "class_bad": class_bad,
        })

    # Random stress block for higher n with the new bN candidate.
    rng = random.Random(20260301)
    summary_rand = []

    for n, max_e, samples in RANDOM_CONFIGS:
        phi_n = euler_phi(n)
        seen = 0
        ok_goal = 0
        ok_bN = 0

        while seen < samples:
            E = tuple(rng.randint(1, max_e) for _ in range(n - 1))
            if math.gcd(*E) != 1:
                continue
            if not any(e % n == 0 for e in E):
                continue

            seen += 1
            out = evaluate_tuple_bounds(n, phi_n, E)
            t = out["tuple_data"]
            if t["x0"] >= phi_n:
                ok_goal += 1
            if out["ok"]["bN"]:
                ok_bN += 1

        summary_rand.append({
            "n": n,
            "phi": phi_n,
            "samples": seen,
            "ok_goal": ok_goal,
            "ok_bN": ok_bN,
            "k_n": (n - 1) if ((n - 1) % 2 == 1) else (n - 2),
        })

    with open(OUT_ROWS, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    lines = []
    lines.append("# Case-2 Signature U_s Checker (v2, upgraded)")
    lines.append("")
    lines.append("Closed-form classwise candidates:")
    lines.append("- `U_s^cap`: capacity (`sum_e (1+delta_e)gcd(e,n) >= n`).")
    lines.append("- `U_s^solv`: solvable branch capacity (`sum_e s_e(sig) >= n`).")
    lines.append("- `U_s^b3`: `UB3>=n`, where `UB3=V1-V2+V3`.")
    lines.append("- `U_s^b5`: `UB5>=n`, where `UB5=V1-V2+V3-V4+V5`.")
    lines.append("- `U_s^bN`: dynamic odd Bonferroni bound: `UB_k>=n` with `k=max odd <= n-1`.")
    lines.append("- `U_s^hyb5`: `cap & solv & b5`.")
    lines.append("- `U_s^hybN`: `cap & solv & bN`.")
    lines.append("- `U_s^cov`: exact baseline (`cover_s=n`).")
    lines.append("")
    lines.append("Tuple-level forcing check:")
    lines.append("- `sum_s U_s F_s <= n(B_div-(n-1))`.")
    lines.append("")

    lines.append("## Exhaustive (Case-2 grids)")
    lines.append("| n | case2 tuples | x0>=phi | cap | solv | b3 | b5 | bN | hyb5 | hybN | cov |")
    lines.append("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")

    for s in summary_exh:
        n = s["n"]
        t = s["tuples"]
        ob = s["ok_bound"]
        lines.append(
            f"| {n} | {t} | {s['ok_goal']}/{t} | {ob['cap']}/{t} | {ob['solv']}/{t} | "
            f"{ob['b3']}/{t} | {ob['b5']}/{t} | {ob['bN']}/{t} | {ob['hyb5']}/{t} | "
            f"{ob['hybN']}/{t} | {ob['cov']}/{t} |"
        )

    lines.append("")
    lines.append("## Random Stress (higher n)")
    lines.append("| n | k_n | samples | x0>=phi | bN forcing |")
    lines.append("|---:|---:|---:|---:|---:|")
    for s in summary_rand:
        n = s["n"]
        lines.append(
            f"| {n} | {s['k_n']} | {s['samples']} | {s['ok_goal']}/{s['samples']} | {s['ok_bN']}/{s['samples']} |"
        )

    lines.append("")
    lines.append("Artifacts:")
    lines.append(f"- rows: `{OUT_ROWS}`")
    lines.append(f"- summary: `{OUT_SUMMARY}`")

    with open(OUT_SUMMARY, "w") as f:
        f.write("\n".join(lines) + "\n")

    print("Wrote:", OUT_ROWS)
    print("Wrote:", OUT_SUMMARY)


if __name__ == "__main__":
    main()
