#!/usr/bin/env python3
"""
D.3 finite-certification runner for one-parameter Case-2 templates.

Family form:
  E(M) = E_fixed ∪ {M} ∪ E_div

Current intended use: all-distinct branch with E_div={n}.

Given:
  n, fixed list, divisible list, and M0,
builds
  T(F) = {1 <= M < M0 : gcd(M, n*L0)=1}
and checks exact x0(F,M) >= phi(n) for all M in T(F).
"""

import argparse
import csv
from math import gcd


def lcm2(a: int, b: int) -> int:
    return a * b // gcd(a, b)


def lcm_list(vals):
    r = 1
    for v in vals:
        r = lcm2(r, int(v))
    return r


def parse_int_list(s: str):
    s = s.strip()
    if not s:
        return []
    return [int(x.strip()) for x in s.split(',') if x.strip()]


def modinv_prime(a: int, p: int) -> int:
    return pow(a % p, p - 2, p)


def bad_a_for(e: int, b: int, L: int, n: int):
    """Exact bad-a set for one runner e at fiber b.
    Uses 1-element boundary case when (e*b) mod L == 0.
    """
    t = (e * b) // L
    s = (e * b) % L
    inv_e = modinv_prime(e, n)
    a0 = (-t * inv_e) % n
    if s == 0:
        return {a0}
    a1 = ((n - 1 - t) * inv_e) % n
    return {a0, a1}


def compute_x0_case2_oneparam(n: int, fixed, divs, M: int):
    speeds = list(fixed) + [M] + list(divs)
    if gcd(*speeds) != 1:
        return None

    L0 = lcm_list(list(fixed) + list(divs))
    L = L0 * M

    # B_div: fibers that pass all divisible-speed constraints
    B_div = []
    for b in range(L):
        ok = True
        for ed in divs:
            v = (ed * b) % L
            if not (L // n <= v <= (n - 1) * L // n):
                ok = False
                break
        if ok:
            B_div.append(b)

    x0 = 0
    B_safe = 0
    non_div = list(fixed) + [M]
    for b in B_div:
        union_bad = set()
        for e in non_div:
            union_bad |= bad_a_for(e, b, L, n)
        A_b = n - len(union_bad)
        if A_b > 0:
            B_safe += 1
        x0 += A_b

    return {
        "L0": L0,
        "L": L,
        "B_div": len(B_div),
        "B_safe": B_safe,
        "x0": x0,
    }


def main():
    ap = argparse.ArgumentParser(description="D.3 finite-certification runner")
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--fixed", type=str, required=True, help="comma list, e.g. 1,2,3,4")
    ap.add_argument("--div", type=str, default="", help="comma list divisible speeds; default n")
    ap.add_argument("--M0", type=int, required=True, help="finite-threshold from D.3")
    ap.add_argument("--tag", type=str, default="family")
    ap.add_argument("--csv", type=str, default="")
    args = ap.parse_args()

    n = args.n
    fixed = parse_int_list(args.fixed)
    divs = parse_int_list(args.div) if args.div.strip() else [n]

    if n < 3:
        raise SystemExit("n must be >=3")
    if any(e % n == 0 for e in fixed):
        raise SystemExit("fixed speeds must be non-divisible by n")
    if any(ed % n != 0 for ed in divs):
        raise SystemExit("all divisible speeds must be multiples of n")

    L0 = lcm_list(list(fixed) + list(divs))
    R = n * L0
    phi_n = n - 1  # prime-n branch here

    T = [m for m in range(1, args.M0) if gcd(m, R) == 1 and m % n != 0]

    rows = []
    violations = []
    worst = None

    for M in T:
        out = compute_x0_case2_oneparam(n, fixed, divs, M)
        if out is None:
            continue
        ok = out["x0"] >= phi_n
        row = {
            "tag": args.tag,
            "n": n,
            "fixed": tuple(fixed),
            "div": tuple(divs),
            "L0": out["L0"],
            "R": R,
            "M0": args.M0,
            "M": M,
            "B_div": out["B_div"],
            "B_safe": out["B_safe"],
            "x0": out["x0"],
            "phi_n": phi_n,
            "ok": int(ok),
        }
        rows.append(row)
        if not ok:
            violations.append(row)
        if worst is None or out["x0"] < worst["x0"]:
            worst = row

    print("D.3 CERTIFICATION SUMMARY")
    print(f"tag={args.tag}")
    print(f"n={n}, fixed={fixed}, div={divs}")
    print(f"L0={L0}, R=n*L0={R}, M0={args.M0}")
    print(f"|T(F)|={len(T)}")
    print(f"violations={len(violations)}")
    if worst:
        print(f"worst: M={worst['M']} x0={worst['x0']} phi={phi_n} B_safe={worst['B_safe']}")

    if args.csv:
        fields = ["tag", "n", "fixed", "div", "L0", "R", "M0", "M", "B_div", "B_safe", "x0", "phi_n", "ok"]
        with open(args.csv, "w", newline="", encoding="utf-8") as f:
            w = csv.DictWriter(f, fieldnames=fields)
            w.writeheader()
            w.writerows(rows)
        print(f"wrote: {args.csv}")


if __name__ == "__main__":
    main()
