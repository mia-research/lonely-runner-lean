#!/usr/bin/env python3
from __future__ import annotations

import csv
import math
from itertools import product

OUT_ROWS = "/tmp/lrc_case2_c23_c24_rows_v2.csv"
OUT_SUMMARY = "/tmp/lrc_case2_c23_c24_summary_v2.md"

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


def analyze_tuple(E: tuple[int, ...], n: int):
    L = math.lcm(*E)
    N = n * L
    lo = L
    hi = (n - 1) * L

    E_div = [e for e in E if e % n == 0]
    E_non = [e for e in E if e % n != 0]
    m = len(E_non)

    B_div = []
    for b in range(L):
        ok_div = True
        for e in E_div:
            r = (e * b) % N
            if r < lo or r > hi:
                ok_div = False
                break
        if ok_div:
            B_div.append(b)

    B_div_size = len(B_div)

    C_bad = 0
    I_bad = 0
    P_bad = 0
    T_bad = 0

    x0 = 0
    B_safe = 0
    min_I_bad = None

    for b in B_div:
        q = []
        A_b = 0
        for a in range(n):
            k = a * L + b
            qa = 0
            for e in E_non:
                r = (e * k) % N
                if r < lo or r > hi:
                    qa += 1
            q.append(qa)
            if qa == 0:
                A_b += 1

        if A_b > 0:
            B_safe += 1
        else:
            C_bad += 1
            I = sum(q)
            P = sum(v * (v - 1) // 2 for v in q)
            T = sum(v * (v - 1) * (v - 2) // 6 for v in q)
            I_bad += I
            P_bad += P
            T_bad += T
            if min_I_bad is None or I < min_I_bad:
                min_I_bad = I

        x0 += A_b

    phi_n = euler_phi(n)

    lhs = n * C_bad
    rhs_I = I_bad
    rhs_IP = I_bad - (2 / m) * P_bad if m > 0 else 0.0
    rhs_IPT = I_bad - P_bad + T_bad

    target = n * (B_div_size - (n - 1))

    return {
        "n": n,
        "phi_n": phi_n,
        "e_tuple": " ".join(map(str, E)),
        "m_non": m,
        "L": L,
        "N": N,
        "B_div": B_div_size,
        "B_safe": B_safe,
        "C_bad": C_bad,
        "x0": x0,
        "I_bad": I_bad,
        "P_bad": P_bad,
        "T_bad": T_bad,
        "min_I_bad": min_I_bad if min_I_bad is not None else "NA",
        "ineq_c23_i": int(lhs <= rhs_I + 1e-9),
        "ineq_c23_ip": int(lhs <= rhs_IP + 1e-9),
        "ineq_c23_ipt": int(lhs <= rhs_IPT + 1e-9),
        "c2main_from_I": int(rhs_I <= target + 1e-9),
        "c2main_from_IP": int(rhs_IP <= target + 1e-9),
        "c2main_from_IPT": int(rhs_IPT <= target + 1e-9),
        "margin_c2main_I": target - rhs_I,
        "margin_c2main_IP": target - rhs_IP,
        "margin_c2main_IPT": target - rhs_IPT,
        "goal_x0_ge_phi": int(x0 >= phi_n),
    }


def main() -> None:
    rows = []
    summary = []

    for n, max_e in MAX_E_BY_N.items():
        total = 0

        agg = {
            "ok_goal": 0,
            "ok_c23_i": 0,
            "ok_c23_ip": 0,
            "ok_c23_ipt": 0,
            "ok_c2main_I": 0,
            "ok_c2main_IP": 0,
            "ok_c2main_IPT": 0,
            "min_margin_I": None,
            "min_margin_IP": None,
            "min_margin_IPT": None,
            "min_badfiber_load": None,
            "ex_fail_IPT": [],
        }

        for E in product(range(1, max_e + 1), repeat=n - 1):
            if math.gcd(*E) != 1:
                continue
            if not any(e % n == 0 for e in E):
                continue

            total += 1
            r = analyze_tuple(E, n)
            rows.append(r)

            agg["ok_goal"] += r["goal_x0_ge_phi"]
            agg["ok_c23_i"] += r["ineq_c23_i"]
            agg["ok_c23_ip"] += r["ineq_c23_ip"]
            agg["ok_c23_ipt"] += r["ineq_c23_ipt"]
            agg["ok_c2main_I"] += r["c2main_from_I"]
            agg["ok_c2main_IP"] += r["c2main_from_IP"]
            agg["ok_c2main_IPT"] += r["c2main_from_IPT"]

            for key, val in [
                ("min_margin_I", r["margin_c2main_I"]),
                ("min_margin_IP", r["margin_c2main_IP"]),
                ("min_margin_IPT", r["margin_c2main_IPT"]),
            ]:
                if agg[key] is None or val < agg[key]:
                    agg[key] = val

            if r["min_I_bad"] != "NA":
                v = int(r["min_I_bad"])
                if agg["min_badfiber_load"] is None or v < agg["min_badfiber_load"]:
                    agg["min_badfiber_load"] = v

            if r["c2main_from_IPT"] == 0 and len(agg["ex_fail_IPT"]) < 6:
                agg["ex_fail_IPT"].append((E, r["B_div"], r["B_safe"], r["I_bad"], r["P_bad"], r["T_bad"], r["margin_c2main_IPT"]))

        summary.append({"n": n, "total": total, **agg})

    with open(OUT_ROWS, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    lines = []
    lines.append("# C2.3/C2.4 Inequality Check (v2)")
    lines.append("")
    lines.append("Bad-fiber moments:")
    lines.append("- `C_bad = #{b in B_div : A_b=0}`")
    lines.append("- `I_bad = sum_{bad b} sum_a q_a(b)`")
    lines.append("- `P_bad = sum_{bad b} sum_a C(q_a(b),2)`")
    lines.append("- `T_bad = sum_{bad b} sum_a C(q_a(b),3)`")
    lines.append("")
    lines.append("C2.3 tested inequalities:")
    lines.append("- `n C_bad <= I_bad`")
    lines.append("- `n C_bad <= I_bad - (2/m)P_bad` (m=|E_non|)")
    lines.append("- `n C_bad <= I_bad - P_bad + T_bad`")
    lines.append("")
    lines.append("C2-main sufficiency candidates tested:")
    lines.append("- (A) `I_bad <= n(B_div-(n-1))`")
    lines.append("- (B) `I_bad - (2/m)P_bad <= n(B_div-(n-1))`")
    lines.append("- (C) `I_bad - P_bad + T_bad <= n(B_div-(n-1))`")
    lines.append("")
    lines.append("| n | case2 tuples | x0>=phi | C2.3(I) | C2.3(I,P) | C2.3(I,P,T) | C2-main(A) | C2-main(B) | C2-main(C) | min bad-fiber I_b |")
    lines.append("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")

    for s in summary:
        lines.append(
            f"| {s['n']} | {s['total']} | {s['ok_goal']}/{s['total']} | {s['ok_c23_i']}/{s['total']} | "
            f"{s['ok_c23_ip']}/{s['total']} | {s['ok_c23_ipt']}/{s['total']} | {s['ok_c2main_I']}/{s['total']} | "
            f"{s['ok_c2main_IP']}/{s['total']} | {s['ok_c2main_IPT']}/{s['total']} | {s['min_badfiber_load']} |"
        )

    lines.append("")
    lines.append("## Min margins for C2-main candidates")
    for s in summary:
        lines.append(
            f"- n={s['n']}: min margins A={s['min_margin_I']}, B={s['min_margin_IP']}, C={s['min_margin_IPT']}"
        )

    lines.append("")
    lines.append("## Example failures of C2-main(C)")
    for s in summary:
        if s["ok_c2main_IPT"] == s["total"]:
            lines.append(f"- n={s['n']}: none")
        else:
            ex = "; ".join(
                [
                    f"{E} (B_div={Bd}, B_safe={Bs}, I={I}, P={P}, T={T}, margin={m})"
                    for E, Bd, Bs, I, P, T, m in s["ex_fail_IPT"]
                ]
            )
            lines.append(f"- n={s['n']}: {ex}")

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
