#!/usr/bin/env python3
"""
Batch D.3 certification for all all-distinct one-divisible templates.

Template class:
  n prime,
  E(M) = E_fixed ∪ {M} ∪ {n},
  E_fixed is a subset of {1,...,n-1} with size n-3 (distinct fixed speeds).

For each template F:
  1) derive D.2-band parameters (A, lambda, beta, a_F, b_F)
  2) derive M0(F)
  3) build finite check-set T(F)
  4) exact-check x0(F,M) >= phi(n) for all M in T(F)

Outputs:
  - rows CSV with per-template certification details
  - checks CSV with per-M checks
  - markdown summary
"""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from math import ceil, gcd
from pathlib import Path
from typing import List, Tuple


def lcm2(a: int, b: int) -> int:
    return a * b // gcd(a, b)


def lcm_list(vals: List[int]) -> int:
    r = 1
    for v in vals:
        r = lcm2(r, int(v))
    return r


def modinv_prime(a: int, p: int) -> int:
    return pow(a % p, p - 2, p)


def bad_a_for(e: int, b: int, L: int, n: int):
    t = (e * b) // L
    s = (e * b) % L
    inv_e = modinv_prime(e, n)
    a0 = (-t * inv_e) % n
    if s == 0:
        return {a0}
    a1 = ((n - 1 - t) * inv_e) % n
    return {a0, a1}


def compute_x0_case2_oneparam(n: int, fixed: List[int], divs: List[int], M: int):
    speeds = list(fixed) + [M] + list(divs)
    if gcd(*speeds) != 1:
        return None

    L0 = lcm_list(list(fixed) + list(divs))
    L = L0 * M

    b_lo = L // n
    b_hi = (n - 1) * L // n

    B_div = []
    for b in range(b_lo, b_hi + 1):
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


@dataclass
class TemplateCert:
    n: int
    fixed: Tuple[int, ...]
    e_max: int
    L0: int
    A: Fraction
    lam: int
    beta: int
    a_F: Fraction
    b_F: Fraction
    M0: int
    R: int
    T_size: int
    violations: int
    worst_M: int
    worst_x0: int
    worst_Bsafe: int


def certify_template(n: int, fixed: Tuple[int, ...]) -> Tuple[TemplateCert, List[dict]]:
    fixed_list = list(fixed)
    e_max = max(fixed_list)
    divs = [n]
    L0 = lcm_list(fixed_list + divs)

    A = Fraction(n - 1, n) - Fraction(1, L0)
    lam = int(2 * L0 * Fraction(n - e_max, n * e_max))
    beta = 1

    a_F = A * lam
    b_F = A * beta - (4 * L0 + 2)

    rhs = Fraction(n - 1) - b_F
    M0 = max(1, ceil(rhs / a_F))
    R = n * L0

    T = [m for m in range(1, M0) if gcd(m, R) == 1 and m % n != 0]

    checks = []
    violations = 0
    worst = None

    for M in T:
        out = compute_x0_case2_oneparam(n, fixed_list, divs, M)
        if out is None:
            continue
        ok = out["x0"] >= (n - 1)
        row = {
            "n": n,
            "fixed": "(" + ",".join(map(str, fixed)) + ")",
            "L0": L0,
            "e_max": e_max,
            "M": M,
            "M0": M0,
            "R": R,
            "x0": out["x0"],
            "phi_n": n - 1,
            "B_safe": out["B_safe"],
            "B_div": out["B_div"],
            "ok": int(ok),
        }
        checks.append(row)
        if not ok:
            violations += 1
        if worst is None or out["x0"] < worst["x0"]:
            worst = {"M": M, "x0": out["x0"], "B_safe": out["B_safe"]}

    if worst is None:
        worst = {"M": -1, "x0": 10**9, "B_safe": -1}

    cert = TemplateCert(
        n=n,
        fixed=fixed,
        e_max=e_max,
        L0=L0,
        A=A,
        lam=lam,
        beta=beta,
        a_F=a_F,
        b_F=b_F,
        M0=M0,
        R=R,
        T_size=len(T),
        violations=violations,
        worst_M=worst["M"],
        worst_x0=worst["x0"],
        worst_Bsafe=worst["B_safe"],
    )
    return cert, checks


def run_batch(n_values: List[int]):
    certs: List[TemplateCert] = []
    checks: List[dict] = []

    for n in n_values:
        print(f"[batch] n={n}: enumerating templates")
        templates = list(combinations(range(1, n), n - 3))
        print(f"[batch] n={n}: total templates={len(templates)}")

        for i, fixed in enumerate(templates, 1):
            cert, crows = certify_template(n, fixed)
            certs.append(cert)
            checks.extend(crows)
            print(
                f"  [{i}/{len(templates)}] fixed={fixed} "
                f"M0={cert.M0} |T|={cert.T_size} violations={cert.violations} "
                f"worst_x0={cert.worst_x0}"
            )

    return certs, checks


def write_outputs(base_dir: Path, certs: List[TemplateCert], checks: List[dict], tag: str):
    rows_csv = base_dir / f"lrc_case2_d3_batch_rows_{tag}.csv"
    checks_csv = base_dir / f"lrc_case2_d3_batch_checks_{tag}.csv"
    summary_md = base_dir / f"lrc_case2_d3_batch_summary_{tag}.md"

    with rows_csv.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow([
            "n", "fixed", "e_max", "L0", "A", "lambda", "beta",
            "a_F", "b_F", "M0", "R", "T_size", "violations",
            "worst_M", "worst_x0", "worst_Bsafe",
        ])
        for c in certs:
            w.writerow([
                c.n,
                "(" + ",".join(map(str, c.fixed)) + ")",
                c.e_max,
                c.L0,
                str(c.A),
                c.lam,
                c.beta,
                str(c.a_F),
                str(c.b_F),
                c.M0,
                c.R,
                c.T_size,
                c.violations,
                c.worst_M,
                c.worst_x0,
                c.worst_Bsafe,
            ])

    if checks:
        with checks_csv.open("w", newline="", encoding="utf-8") as f:
            fields = list(checks[0].keys())
            w = csv.DictWriter(f, fieldnames=fields)
            w.writeheader()
            w.writerows(checks)

    by_n = {}
    for c in certs:
        by_n.setdefault(c.n, []).append(c)

    with summary_md.open("w", encoding="utf-8") as f:
        f.write("# D.3 Batch Certification Summary\n\n")
        for n in sorted(by_n):
            arr = by_n[n]
            v = sum(c.violations for c in arr)
            t = sum(c.T_size for c in arr)
            worst_x0 = min(c.worst_x0 for c in arr)
            max_M0 = max(c.M0 for c in arr)
            f.write(f"## n={n}\n")
            f.write(f"- templates: {len(arr)}\n")
            f.write(f"- total finite checks |T|: {t}\n")
            f.write(f"- total violations: {v}\n")
            f.write(f"- min worst_x0 across templates: {worst_x0}\n")
            f.write(f"- max M0 across templates: {max_M0}\n\n")

        f.write("## Artifacts\n")
        f.write(f"- rows: `{rows_csv.name}`\n")
        f.write(f"- checks: `{checks_csv.name}`\n")
        f.write(f"- summary: `{summary_md.name}`\n")

    return rows_csv, checks_csv, summary_md


def main():
    ap = argparse.ArgumentParser(description="Batch D.3 certify all all-distinct templates")
    ap.add_argument("--n-list", type=str, default="7,11")
    ap.add_argument("--tag", type=str, default="v1")
    ap.add_argument("--out-dir", type=str, default=".")
    args = ap.parse_args()

    n_values = [int(x.strip()) for x in args.n_list.split(",") if x.strip()]
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    certs, checks = run_batch(n_values)
    rows_csv, checks_csv, summary_md = write_outputs(out_dir, certs, checks, args.tag)

    print("\n[done]")
    print(f"rows:    {rows_csv}")
    print(f"checks:  {checks_csv}")
    print(f"summary: {summary_md}")


if __name__ == "__main__":
    main()
