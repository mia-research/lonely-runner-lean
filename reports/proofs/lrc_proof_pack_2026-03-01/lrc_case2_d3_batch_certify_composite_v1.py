#!/usr/bin/env python3
"""
Composite-safe batch D.3 certification for all-distinct one-divisible templates.

Supports n not necessarily prime by avoiding inverse-based bad-a formulas.
Uses exact congruence masks per runner/state.
"""

from __future__ import annotations

import argparse
import csv
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from math import ceil, gcd
from pathlib import Path
from typing import Dict, List, Tuple


def lcm2(a: int, b: int) -> int:
    return a * b // gcd(a, b)


def lcm_list(vals: List[int]) -> int:
    r = 1
    for v in vals:
        r = lcm2(r, int(v))
    return r


def precompute_runner_masks(n: int, e: int) -> List[List[int]]:
    """Return masks[t][z] for t in 0..e-1, z in {0,1} (s==0 flag).

    bad iff q==0 OR (q==n-1 and s>0), where q=(e*a+t) mod n.
    """
    masks = [[0, 0] for _ in range(e)]
    for t in range(e):
        for z in (0, 1):
            mask = 0
            for a in range(n):
                q = (e * a + t) % n
                bad = (q == 0) or (q == n - 1 and z == 0)
                if bad:
                    mask |= 1 << a
            masks[t][z] = mask
    return masks


def compute_x0_fast_generic(n: int, fixed: List[int], M: int, L0: int):
    """Exact x0 for E = fixed U {M} U {n} with contiguous B_div for divisor n."""
    L = L0 * M
    b_lo = L // n
    b_hi = (n - 1) * L // n

    non_div = fixed + [M]
    tables: Dict[int, List[List[int]]] = {e: precompute_runner_masks(n, e) for e in non_div}

    x0 = 0
    B_safe = 0

    for b in range(b_lo, b_hi + 1):
        union_mask = 0
        for e in non_div:
            eb = e * b
            t = eb // L
            s = eb - t * L
            z = 1 if s == 0 else 0
            union_mask |= tables[e][t][z]

        A_b = n - union_mask.bit_count()
        x0 += A_b
        if A_b > 0:
            B_safe += 1

    B_div = b_hi - b_lo + 1
    return {"x0": x0, "B_safe": B_safe, "B_div": B_div}


@dataclass
class TemplateCert:
    n: int
    fixed: Tuple[int, ...]
    e_max: int
    L0: int
    A: str
    lam: int
    beta: int
    a_F: str
    b_F: str
    M0: int
    R: int
    T_size: int
    violations: int
    worst_M: int
    worst_x0: int
    worst_Bsafe: int


def certify_template(task):
    n, fixed = task
    fixed = tuple(fixed)
    fixed_list = list(fixed)
    e_max = max(fixed_list)

    L0 = lcm_list(fixed_list + [n])
    A = Fraction(n - 1, n) - Fraction(1, L0)
    lam = int(2 * L0 * Fraction(n - e_max, n * e_max))
    beta = 1

    if lam <= 0:
        a_F = Fraction(1, 1)
        b_F = Fraction(-(10**6), 1)
        M0 = 1
    else:
        a_F = A * lam
        b_F = A * beta - (4 * L0 + 2)
        rhs = Fraction(n - 1) - b_F
        M0 = max(1, ceil(rhs / a_F))

    R = n * L0
    # D.3 admissible parameters
    T = [m for m in range(1, M0) if gcd(m, R) == 1]

    checks = []
    violations = 0
    worst = None

    for M in T:
        out = compute_x0_fast_generic(n, fixed_list, M, L0)
        phi_n = n - 1 if all(gcd(k, n) == 1 for k in range(1, n) if gcd(k, n) == 1) and False else None
        # Use actual Euler phi for threshold
        phi = sum(1 for j in range(1, n + 1) if gcd(j, n) == 1)
        ok = out["x0"] >= phi
        checks.append({
            "n": n,
            "fixed": "(" + ",".join(map(str, fixed)) + ")",
            "L0": L0,
            "e_max": e_max,
            "M": M,
            "M0": M0,
            "R": R,
            "x0": out["x0"],
            "phi_n": phi,
            "B_safe": out["B_safe"],
            "B_div": out["B_div"],
            "ok": int(ok),
        })

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
        A=str(A),
        lam=lam,
        beta=beta,
        a_F=str(a_F),
        b_F=str(b_F),
        M0=M0,
        R=R,
        T_size=len(T),
        violations=violations,
        worst_M=worst["M"],
        worst_x0=worst["x0"],
        worst_Bsafe=worst["B_safe"],
    )
    return cert, checks


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
        for c in sorted(certs, key=lambda x: (x.n, x.fixed)):
            w.writerow([
                c.n,
                "(" + ",".join(map(str, c.fixed)) + ")",
                c.e_max,
                c.L0,
                c.A,
                c.lam,
                c.beta,
                c.a_F,
                c.b_F,
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
        f.write("# D.3 Composite-Safe Batch Certification Summary\n\n")
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
    ap = argparse.ArgumentParser(description="Composite-safe batch D.3 certification")
    ap.add_argument("--n-list", type=str, default="8,9,10")
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--tag", type=str, default="n8n9n10_v1")
    ap.add_argument("--out-dir", type=str, default=".")
    args = ap.parse_args()

    n_values = [int(x.strip()) for x in args.n_list.split(",") if x.strip()]
    tasks = []
    for n in n_values:
        temps = list(combinations(range(1, n), n - 3))
        print(f"[build] n={n} templates={len(temps)}")
        tasks.extend([(n, t) for t in temps])

    certs: List[TemplateCert] = []
    checks: List[dict] = []

    print(f"[run] total templates={len(tasks)} workers={args.workers}")
    done = 0
    with ProcessPoolExecutor(max_workers=args.workers) as ex:
        futs = {ex.submit(certify_template, task): task for task in tasks}
        for fut in as_completed(futs):
            cert, crows = fut.result()
            certs.append(cert)
            checks.extend(crows)
            done += 1
            print(f"  [{done}/{len(tasks)}] n={cert.n} fixed={cert.fixed} |T|={cert.T_size} violations={cert.violations} worst_x0={cert.worst_x0}")

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    rows_csv, checks_csv, summary_md = write_outputs(out_dir, certs, checks, args.tag)

    print("\n[done]")
    print(f"rows:    {rows_csv}")
    print(f"checks:  {checks_csv}")
    print(f"summary: {summary_md}")


if __name__ == "__main__":
    main()
