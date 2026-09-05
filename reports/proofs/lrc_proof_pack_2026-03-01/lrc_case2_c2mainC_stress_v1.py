#!/usr/bin/env python3
from __future__ import annotations

import csv
import math
import random

OUT_ROWS = "/tmp/lrc_case2_c2mainC_stress_rows_v1.csv"
OUT_SUMMARY = "/tmp/lrc_case2_c2mainC_stress_summary_v1.md"

RANDOM_PLAN = [
    (8, 12000, 32, 2500),
    (9, 8000, 36, 2500),
    (10, 6000, 40, 2500),
    (11, 3000, 44, 2500),
    (12, 2000, 48, 2500),
]


def check_tuple(E: tuple[int, ...], n: int):
    L = math.lcm(*E)
    N = n * L
    lo = L
    hi = (n - 1) * L

    E_div = [e for e in E if e % n == 0]
    E_non = [e for e in E if e % n != 0]

    B_div = []
    for b in range(L):
        ok = True
        for e in E_div:
            r = (e * b) % N
            if r < lo or r > hi:
                ok = False
                break
        if ok:
            B_div.append(b)

    Bdiv = len(B_div)
    C_bad = 0
    I = P = T = 0

    for b in B_div:
        safe = False
        qvals = []
        for a in range(n):
            k = a * L + b
            q = 0
            for e in E_non:
                r = (e * k) % N
                if r < lo or r > hi:
                    q += 1
            qvals.append(q)
            if q == 0:
                safe = True
        if safe:
            continue
        C_bad += 1
        I += sum(qvals)
        P += sum(v * (v - 1) // 2 for v in qvals)
        T += sum(v * (v - 1) * (v - 2) // 6 for v in qvals)

    lhs = I - P + T
    rhs = n * (Bdiv - (n - 1))
    return lhs <= rhs, L, Bdiv, C_bad, I, P, T, lhs, rhs


def main() -> None:
    random.seed(0)
    rows = []
    summary = []

    for n, target_samples, max_e, L_cap in RANDOM_PLAN:
        checked = 0
        tries = 0
        viol = 0
        first_viol = None

        while checked < target_samples and tries < target_samples * 200:
            tries += 1
            E = tuple(random.randint(1, max_e) for _ in range(n - 1))
            if math.gcd(*E) != 1:
                continue
            if not any(e % n == 0 for e in E):
                continue
            L = math.lcm(*E)
            if L > L_cap:
                continue

            checked += 1
            ok, L, Bdiv, C_bad, I, P, T, lhs, rhs = check_tuple(E, n)
            rows.append({
                "n": n,
                "e_tuple": " ".join(map(str, E)),
                "L": L,
                "B_div": Bdiv,
                "C_bad": C_bad,
                "I_bad": I,
                "P_bad": P,
                "T_bad": T,
                "lhs_IPT": lhs,
                "rhs_target": rhs,
                "ok": int(ok),
                "margin": rhs - lhs,
            })
            if not ok:
                viol += 1
                if first_viol is None:
                    first_viol = (E, L, Bdiv, C_bad, I, P, T, lhs, rhs)
                break

        summary.append({
            "n": n,
            "target_samples": target_samples,
            "checked": checked,
            "tries": tries,
            "max_e": max_e,
            "L_cap": L_cap,
            "viol": viol,
            "first_viol": first_viol,
        })

    with open(OUT_ROWS, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()) if rows else ["n"])
        w.writeheader()
        w.writerows(rows)

    lines = ["# C2-main(C) Random Stress (v1)", "", "Condition tested:", "- `I_bad - P_bad + T_bad <= n(B_div-(n-1))`", ""]
    lines.append("| n | checked | target | max_e | L_cap | violations |")
    lines.append("|---:|---:|---:|---:|---:|---:|")
    for s in summary:
        lines.append(f"| {s['n']} | {s['checked']} | {s['target_samples']} | {s['max_e']} | {s['L_cap']} | {s['viol']} |")

    lines.append("")
    lines.append("## First violation per n")
    for s in summary:
        if s["first_viol"] is None:
            lines.append(f"- n={s['n']}: none")
        else:
            lines.append(f"- n={s['n']}: {s['first_viol']}")

    lines.append("")
    lines.append("Artifacts:")
    lines.append(f"- rows: `{OUT_ROWS}`")
    lines.append(f"- summary: `{OUT_SUMMARY}`")

    with open(OUT_SUMMARY, "w") as f:
        f.write("\n".join(lines) + "\n")

    print("FINAL")
    print("rows", OUT_ROWS)
    print("summary", OUT_SUMMARY)


if __name__ == "__main__":
    main()
