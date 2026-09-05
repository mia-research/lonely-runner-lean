#!/usr/bin/env python3
from __future__ import annotations

import csv
import math
from itertools import product

OUT_ROWS = "/tmp/lrc_case2_c2main_bounds_rows_v1.csv"
OUT_SUMMARY = "/tmp/lrc_case2_c2main_bounds_summary_v1.md"

# Keep the same bounded exhaustive grids used in existing Case-2 scans.
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


def single_div_safe_count(f: int, n: int, L: int) -> int:
    """Exact |{b mod L : q <= (f*b mod L) <= (n-1)q}| where q=L/n."""
    q = L // n
    d = math.gcd(f, L)
    lo = (q + d - 1) // d
    hi = ((n - 1) * q) // d
    if hi < lo:
        return 0
    return d * (hi - lo + 1)


def bounds_for_tuple(E: tuple[int, ...], n: int):
    L = math.lcm(*E)
    N = n * L
    q = L // n
    phi_n = euler_phi(n)

    E_div = tuple(e for e in E if e % n == 0)
    E_non = tuple(e for e in E if e % n != 0)
    f_list = tuple(e // n for e in E_div)

    # B_div exact and per-b exact A_b / lower-bounds
    B_div_exact = 0
    x0_exact = 0
    lb_x0_fiber = 0

    # Keep b-level A_b lower bound stats for diagnostics
    min_Ab_exact = n
    min_Ab_lb = n

    loN = L
    hiN = (n - 1) * L

    # anchor b-set from divisible constraints on b = j*q
    d_anchor = [n // math.gcd(n, f) for f in f_list]
    anchor_js = [j for j in range(1, n) if all(j % d != 0 for d in d_anchor)]
    anchor_bs = {j * q for j in anchor_js}
    lb_Bdiv_anchor = len(anchor_js)

    # exact B_div + exact x0 + fiber-union lower bound
    for b in range(L):
        ok_div = True
        for e in E_div:
            r = (e * b) % N
            if r < loN or r > hiN:
                ok_div = False
                break
        if not ok_div:
            continue

        B_div_exact += 1

        # exact A_b and a fiber-level union lower bound
        bad_sum = 0
        Ab = 0
        for e in E_non:
            bad_e = 0
            for a in range(n):
                k = a * L + b
                r = (e * k) % N
                if r < loN or r > hiN:
                    bad_e += 1
            bad_sum += bad_e

        Ab_lb = max(0, n - bad_sum)
        lb_x0_fiber += Ab_lb
        if Ab_lb < min_Ab_lb:
            min_Ab_lb = Ab_lb

        for a in range(n):
            k = a * L + b
            ok_non = True
            for e in E_non:
                r = (e * k) % N
                if r < loN or r > hiN:
                    ok_non = False
                    break
            if ok_non:
                Ab += 1

        if Ab < min_Ab_exact:
            min_Ab_exact = Ab

        x0_exact += Ab

    # explicit |B_div| lower bounds
    single_counts = [single_div_safe_count(f, n, L) for f in f_list]
    if single_counts:
        lb_Bdiv_union1 = max(0, sum(single_counts) - (len(single_counts) - 1) * L)
    else:
        lb_Bdiv_union1 = 0
    lb_Bdiv = max(lb_Bdiv_union1, lb_Bdiv_anchor)

    # uniform |A_b| lower bound across all b (simple and explicit)
    gsum = sum(math.gcd(e, n) for e in E_non)
    lb_Ab_uniform = max(0, n - 2 * gsum)

    # product lower bound using explicit LB_Bdiv and uniform LB_Ab
    lb_x0_uniform = lb_Bdiv * lb_Ab_uniform

    # anchor-fiber lower bound (compute exact A_b on anchors; still explicit subset witness)
    x0_anchor_exact = 0
    for b in anchor_bs:
        Ab = 0
        for a in range(n):
            k = a * L + b
            ok_non = True
            for e in E_non:
                r = (e * k) % N
                if r < loN or r > hiN:
                    ok_non = False
                    break
            if ok_non:
                Ab += 1
        x0_anchor_exact += Ab

    return {
        "n": n,
        "phi_n": phi_n,
        "e_tuple": " ".join(map(str, E)),
        "L": L,
        "N": N,
        "num_div": len(E_div),
        "num_non": len(E_non),
        "B_div_exact": B_div_exact,
        "x0_exact": x0_exact,
        "lb_Bdiv_union1": lb_Bdiv_union1,
        "lb_Bdiv_anchor": lb_Bdiv_anchor,
        "lb_Bdiv": lb_Bdiv,
        "lb_Ab_uniform": lb_Ab_uniform,
        "lb_x0_uniform": lb_x0_uniform,
        "lb_x0_fiber": lb_x0_fiber,
        "x0_anchor_exact": x0_anchor_exact,
        "min_Ab_exact": min_Ab_exact,
        "min_Ab_lb": min_Ab_lb,
        "proves_uniform": int(lb_x0_uniform >= phi_n),
        "proves_fiber": int(lb_x0_fiber >= phi_n),
        "proves_anchor": int(x0_anchor_exact >= phi_n),
    }


def main() -> None:
    rows = []
    summary = []

    for n, max_e in MAX_E_BY_N.items():
        phi_n = euler_phi(n)
        total = 0
        proves_uniform = 0
        proves_fiber = 0
        proves_anchor = 0

        min_Bdiv_exact = None
        min_lb_Bdiv = None
        min_lb_Ab_uniform = None
        min_lb_x0_uniform = None
        min_lb_x0_fiber = None
        min_x0_exact = None

        ex_fail_uniform = []
        ex_fail_fiber = []

        for E in product(range(1, max_e + 1), repeat=n - 1):
            if math.gcd(*E) != 1:
                continue
            if not any(e % n == 0 for e in E):
                continue

            total += 1
            r = bounds_for_tuple(E, n)
            rows.append(r)

            proves_uniform += r["proves_uniform"]
            proves_fiber += r["proves_fiber"]
            proves_anchor += r["proves_anchor"]

            v = r["B_div_exact"]
            if min_Bdiv_exact is None or v < min_Bdiv_exact:
                min_Bdiv_exact = v
            v = r["lb_Bdiv"]
            if min_lb_Bdiv is None or v < min_lb_Bdiv:
                min_lb_Bdiv = v
            v = r["lb_Ab_uniform"]
            if min_lb_Ab_uniform is None or v < min_lb_Ab_uniform:
                min_lb_Ab_uniform = v
            v = r["lb_x0_uniform"]
            if min_lb_x0_uniform is None or v < min_lb_x0_uniform:
                min_lb_x0_uniform = v
            v = r["lb_x0_fiber"]
            if min_lb_x0_fiber is None or v < min_lb_x0_fiber:
                min_lb_x0_fiber = v
            v = r["x0_exact"]
            if min_x0_exact is None or v < min_x0_exact:
                min_x0_exact = v

            if r["proves_uniform"] == 0 and len(ex_fail_uniform) < 6:
                ex_fail_uniform.append((E, r["lb_Bdiv"], r["lb_Ab_uniform"], r["lb_x0_uniform"], r["x0_exact"]))
            if r["proves_fiber"] == 0 and len(ex_fail_fiber) < 6:
                ex_fail_fiber.append((E, r["lb_x0_fiber"], r["x0_exact"]))

        summary.append({
            "n": n,
            "phi": phi_n,
            "tuples": total,
            "proves_uniform": proves_uniform,
            "proves_fiber": proves_fiber,
            "proves_anchor": proves_anchor,
            "min_Bdiv_exact": min_Bdiv_exact,
            "min_lb_Bdiv": min_lb_Bdiv,
            "min_lb_Ab_uniform": min_lb_Ab_uniform,
            "min_lb_x0_uniform": min_lb_x0_uniform,
            "min_lb_x0_fiber": min_lb_x0_fiber,
            "min_x0_exact": min_x0_exact,
            "ex_fail_uniform": ex_fail_uniform,
            "ex_fail_fiber": ex_fail_fiber,
        })

    # write rows
    with open(OUT_ROWS, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    # write summary
    lines = []
    lines.append("# Lemma E Case-2 Explicit Lower-Bound Checker (v1)")
    lines.append("")
    lines.append("Bounds used:")
    lines.append("- `|B_div| >= max(lb_union1, lb_anchor)`")
    lines.append("- `lb_union1 = max(0, sum_i |S_i| - (s-1)L)` where `S_i` is exact single-divisible safe set")
    lines.append("- `lb_anchor = |{j in {1..n-1}: forall i, n !| (f_i j)}|` for anchors `b=jL/n`")
    lines.append("- Uniform fiber bound: `|A_b| >= max(0, n - 2*sum_{e in E_non} gcd(e,n))`")
    lines.append("- Product bound: `x0 >= lb_Bdiv * lb_Ab_uniform`")
    lines.append("- Stronger explicit per-fiber bound: `x0 >= sum_{b in B_div} max(0, n - sum_e bad_e(b))`")
    lines.append("")
    lines.append("| n | phi(n) | case2 tuples | proved by product | proved by per-fiber | proved by anchor-subset | min x0 exact | min lb_x0 product | min lb_x0 per-fiber | min |B_div| exact | min lb_Bdiv |")
    lines.append("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    for s in summary:
        lines.append(
            f"| {s['n']} | {s['phi']} | {s['tuples']} | {s['proves_uniform']}/{s['tuples']} | {s['proves_fiber']}/{s['tuples']} | "
            f"{s['proves_anchor']}/{s['tuples']} | {s['min_x0_exact']} | {s['min_lb_x0_uniform']} | {s['min_lb_x0_fiber']} | "
            f"{s['min_Bdiv_exact']} | {s['min_lb_Bdiv']} |"
        )

    lines.append("")
    lines.append("## Example failures of product bound")
    for s in summary:
        if s["proves_uniform"] == s["tuples"]:
            lines.append(f"- n={s['n']}: none")
        else:
            ex = "; ".join(
                [f"{E} (lb_Bdiv={lbB}, lb_Ab={lbA}, lb_x0={lbx}, x0={x0})" for E, lbB, lbA, lbx, x0 in s["ex_fail_uniform"]]
            )
            lines.append(f"- n={s['n']}: {ex}")

    lines.append("")
    lines.append("## Example failures of per-fiber bound")
    for s in summary:
        if s["proves_fiber"] == s["tuples"]:
            lines.append(f"- n={s['n']}: none")
        else:
            ex = "; ".join([f"{E} (lb_x0_fiber={lb}, x0={x0})" for E, lb, x0 in s["ex_fail_fiber"]])
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
