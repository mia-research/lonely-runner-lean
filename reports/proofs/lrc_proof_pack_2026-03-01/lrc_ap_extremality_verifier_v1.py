#!/usr/bin/env python3
"""
lrc_ap_extremality_verifier_v1.py

Verifies the AP-core extremality conjecture (Lemma E) computationally:
  x_0(E) >= x_0(A_n) = phi(n)  for all gcd-1 tuples E.

For each n=3..8, iterates over the same bounded exhaustive gcd-1 tuple grid
as lrc_s4_inclusion_checker_v1.py, computes exact x_0 (safe count), and records:
  - minimum x_0 observed
  - whether min x_0 == phi(n)
  - which sorted canonical tuples achieve the minimum
  - whether A_n = (1,...,n-1) is always among the minimizers

Key identity used (integer arithmetic only, no Fraction):
  N = n*L where L = lcm(e_list)
  k is safe iff for all e: L <= (e*k mod N) <= (n-1)*L
  (equivalent to 1/n <= {e*k/N} <= (n-1)/n, i.e. NOT strictly dangerous)

Outputs:
  /tmp/lrc_ap_extremality_rows_v1.csv       -- per-tuple data
  /tmp/lrc_ap_extremality_summary_v1.md     -- per-n summary table
  /tmp/lrc_ap_extremality_minimizers_v1.csv -- tuples achieving min x_0
"""

from __future__ import annotations

import csv
import math
from itertools import product

OUT_ROWS       = "/tmp/lrc_ap_extremality_rows_v1.csv"
OUT_SUMMARY    = "/tmp/lrc_ap_extremality_summary_v1.md"
OUT_MINIMIZERS = "/tmp/lrc_ap_extremality_minimizers_v1.csv"

# Same grid bounds as lrc_s4_inclusion_checker_v1.py
MAX_E_BY_N = {
    3: 12,
    4: 9,
    5: 7,
    6: 5,
    7: 4,
    8: 4,
}


def euler_phi(n: int) -> int:
    result = n
    temp = n
    p = 2
    while p * p <= temp:
        if temp % p == 0:
            while temp % p == 0:
                temp //= p
            result -= result // p
        p += 1
    if temp > 1:
        result -= result // temp
    return result


def is_safe_int(e_list: tuple[int, ...], n: int, L: int, N: int, k: int) -> bool:
    """
    True iff lattice point k is safe for all runners in e_list.
    Uses pure integer arithmetic:
      safe iff for all e: L <= (e*k mod N) <= (n-1)*L
    Boundary (= L or (n-1)*L) is SAFE (dangerous is strict inequality).
    """
    lo = L
    hi = (n - 1) * L
    for e in e_list:
        v = (e * k) % N
        if v < lo or v > hi:
            return False
    return True


def compute_x0_int(e_list: tuple[int, ...], n: int) -> tuple[int, int, int]:
    """
    Compute safe count x_0, union size, and N.
    Returns (x_0, union, N).
    """
    L = math.lcm(*e_list)
    N = n * L
    safe = sum(1 for k in range(N) if is_safe_int(e_list, n, L, N, k))
    return safe, N - safe, N


def ap_core(n: int) -> tuple[int, ...]:
    """A_n = (1, 2, ..., n-1)."""
    return tuple(range(1, n))


def run_scan():
    all_rows      = []
    summary_rows  = []
    minimizer_rows = []

    for n in sorted(MAX_E_BY_N):
        max_e  = MAX_E_BY_N[n]
        phi_n  = euler_phi(n)
        An     = ap_core(n)
        An_sorted = tuple(sorted(An))

        min_x0       = None
        total_gcd1   = 0
        violations   = 0       # tuples with x_0 < phi(n)
        min_tuples   = []      # canonical sorted tuples achieving min_x0

        for e_tuple in product(range(1, max_e + 1), repeat=n - 1):
            if math.gcd(*e_tuple) != 1:
                continue
            total_gcd1 += 1

            x0, union, N = compute_x0_int(e_tuple, n)
            L = N // n
            sorted_t = tuple(sorted(e_tuple))

            row = {
                "n": n,
                "e_tuple":      " ".join(map(str, e_tuple)),
                "sorted_tuple": " ".join(map(str, sorted_t)),
                "L":            L,
                "N":            N,
                "x0":           x0,
                "union":        union,
                "phi_n":        phi_n,
                "is_an":        int(sorted_t == An_sorted),
                "x0_minus_phi": x0 - phi_n,
            }
            all_rows.append(row)

            if x0 < phi_n:
                violations += 1

            if min_x0 is None or x0 < min_x0:
                min_x0 = x0
                min_tuples = [sorted_t]
            elif x0 == min_x0 and sorted_t not in min_tuples:
                min_tuples.append(sorted_t)

        an_is_min      = An_sorted in min_tuples
        min_equals_phi = (min_x0 == phi_n)

        summary_rows.append({
            "n":                     n,
            "phi_n":                 phi_n,
            "max_e":                 max_e,
            "total_gcd1":            total_gcd1,
            "min_x0":                min_x0,
            "min_equals_phi_n":      int(min_equals_phi),
            "an_is_minimizer":       int(an_is_min),
            "violations_below_phi":  violations,
            "n_distinct_min_tuples": len(min_tuples),
        })

        for t in sorted(min_tuples):
            minimizer_rows.append({
                "n":               n,
                "phi_n":           phi_n,
                "min_x0":          min_x0,
                "sorted_min_tuple": " ".join(map(str, t)),
                "is_an":           int(t == An_sorted),
            })

        print(f"  n={n}: phi={phi_n}, min_x0={min_x0}, phi==min: {min_equals_phi}, "
              f"An_is_min: {an_is_min}, violations: {violations}, "
              f"distinct_min_tuples: {len(min_tuples)}, total_gcd1: {total_gcd1}")

    return all_rows, summary_rows, minimizer_rows


def write_outputs(all_rows, summary_rows, minimizer_rows):
    with open(OUT_ROWS, "w", newline="") as f:
        if all_rows:
            w = csv.DictWriter(f, fieldnames=list(all_rows[0].keys()))
            w.writeheader()
            w.writerows(all_rows)

    with open(OUT_MINIMIZERS, "w", newline="") as f:
        if minimizer_rows:
            w = csv.DictWriter(f, fieldnames=list(minimizer_rows[0].keys()))
            w.writeheader()
            w.writerows(minimizer_rows)

    lines = []
    lines.append("# AP-Core Extremality Survey (v1)")
    lines.append("")
    lines.append("**Conjecture (Lemma E):** x_0(E) >= phi(n) = x_0(A_n) for all gcd-1 tuples E.")
    lines.append("")
    lines.append("Uses integer arithmetic: k safe iff L <= (e*k mod N) <= (n-1)*L for all e.")
    lines.append("")
    lines.append("## Per-n Results")
    lines.append("")
    lines.append("| n | phi(n) | max_e | gcd-1 tuples | min x_0 | min==phi(n) | A_n minimizer | violations (x_0<phi) | distinct min-tuples |")
    lines.append("|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    for r in summary_rows:
        lines.append(
            f"| {r['n']} | {r['phi_n']} | {r['max_e']} | {r['total_gcd1']} | "
            f"{r['min_x0']} | {'YES' if r['min_equals_phi_n'] else 'NO'} | "
            f"{'YES' if r['an_is_minimizer'] else 'NO'} | "
            f"{r['violations_below_phi']} | {r['n_distinct_min_tuples']} |"
        )
    lines.append("")

    all_ok   = all(r["violations_below_phi"] == 0 for r in summary_rows)
    all_phi  = all(r["min_equals_phi_n"] for r in summary_rows)
    all_an   = all(r["an_is_minimizer"] for r in summary_rows)

    lines.append("## Global Verdict")
    lines.append("")
    lines.append(f"- All tuples satisfy x_0 >= phi(n): **{'YES — Lemma E holds on this grid' if all_ok else 'NO — violations found'}**")
    lines.append(f"- min x_0 == phi(n) for all n:      **{'YES' if all_phi else 'NO'}**")
    lines.append(f"- A_n is always a minimizer:        **{'YES' if all_an else 'NO'}**")
    lines.append("")
    lines.append("## Minimizing Tuples")
    lines.append("")
    lines.append("(All tuples achieving the minimum safe count for each n)")
    lines.append("")
    lines.append("| n | phi(n) | min x_0 | sorted tuple | is A_n |")
    lines.append("|---:|---:|---:|:---|:---:|")
    for r in minimizer_rows:
        lines.append(
            f"| {r['n']} | {r['phi_n']} | {r['min_x0']} | "
            f"`{r['sorted_min_tuple']}` | {'**YES**' if r['is_an'] else 'no'} |"
        )
    lines.append("")
    lines.append("## Interpretation")
    lines.append("")
    lines.append("If violations==0 and min x_0==phi(n) for all n=3..8:")
    lines.append("")
    lines.append("- O_mass = |union D_e|/N is maximized at A_n for all tested n and speeds.")
    lines.append("- x_0(A_n) = phi(n) is the global minimum safe count within the tested grid.")
    lines.append("- This computationally confirms Lemma E for n=3..8.")
    lines.append("- Combined with the analytic proof that x_0(A_n)=phi(n) (Lemma P),")
    lines.append("  an analytic generalization of Lemma E would close Lemma 8.1 and")
    lines.append("  the rational SINGLE theorem for all n.")

    with open(OUT_SUMMARY, "w") as f:
        f.write("\n".join(lines) + "\n")

    print(f"\nOutputs written:")
    print(f"  {OUT_ROWS}")
    print(f"  {OUT_MINIMIZERS}")
    print(f"  {OUT_SUMMARY}")


def main():
    print("AP-Core Extremality Verifier v1")
    print("Scanning gcd-1 tuples for n=3..8 ...")
    all_rows, summary_rows, minimizer_rows = run_scan()
    write_outputs(all_rows, summary_rows, minimizer_rows)
    print("\nDone.")


if __name__ == "__main__":
    main()
