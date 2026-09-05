#!/usr/bin/env python3
"""
lrc_safe_point_enumerator_v1.py

Investigates the phi(n)-Witness Route (Route A toward Lemma E):

For each gcd-1 tuple E = (e_1,...,e_m) and n=3..6, enumerates ALL safe points
(k in Z_N with k not in any D_e), then tests:

  Q: Do the A_n witnesses k=jL (gcd(j,n)=1, j=1..n-1) survive for ALL E?

  If YES for all tuples → Lemma E proved: x_0(E) >= phi(n) via uniform witnesses.
  If NO             → reports which tuples fail, and what safe points they DO have.

Key identity (integer only):
  N = n*L,  k safe iff all e: L <= (e*k mod N) <= (n-1)*L

Outputs:
  /tmp/lrc_safe_point_witness_summary_v1.md  -- per-n summary + global verdict
  /tmp/lrc_safe_point_failures_v1.csv        -- tuples where some A_n witness fails
  /tmp/lrc_safe_point_detail_v1.csv          -- per-tuple: x_0, witness survival
"""

from __future__ import annotations

import csv
import math
from itertools import product

OUT_SUMMARY  = "/tmp/lrc_safe_point_witness_summary_v1.md"
OUT_FAILURES = "/tmp/lrc_safe_point_failures_v1.csv"
OUT_DETAIL   = "/tmp/lrc_safe_point_detail_v1.csv"

MAX_E_BY_N = {
    3: 12,
    4: 9,
    5: 7,
    6: 5,
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
    lo = L
    hi = (n - 1) * L
    for e in e_list:
        v = (e * k) % N
        if v < lo or v > hi:
            return False
    return True


def enumerate_safe_points(e_list: tuple[int, ...], n: int, L: int, N: int) -> list[int]:
    return [k for k in range(N) if is_safe_int(e_list, n, L, N, k)]


def an_witnesses(n: int, L: int) -> list[int]:
    """A_n witnesses: k = j*L for j in {1,...,n-1} with gcd(j,n)=1."""
    return [j * L for j in range(1, n) if math.gcd(j, n) == 1]


def classify_safe_point(k: int, n: int, L: int, N: int) -> str:
    """Express k relative to L. Returns compact label."""
    if k == 0:
        return "0"
    if k % L == 0:
        j = k // L
        g = math.gcd(j, n)
        return f"jL(j={j},gcd={g})"
    # Try k = j * (L // d) for small d
    for d in [2, 3, 4, 5, 6]:
        if L % d == 0:
            sub = L // d
            if k % sub == 0:
                j = k // sub
                return f"j*L/{d}(j={j})"
    return f"other({k})"


def run_scan():
    summary_rows = []
    failure_rows = []
    detail_rows  = []

    for n in sorted(MAX_E_BY_N):
        max_e = MAX_E_BY_N[n]
        phi_n = euler_phi(n)
        An_sorted = tuple(sorted(range(1, n)))

        total_gcd1           = 0
        witnesses_all_safe   = 0
        witnesses_partial    = 0
        witnesses_none_safe  = 0

        for e_tuple in product(range(1, max_e + 1), repeat=n - 1):
            if math.gcd(*e_tuple) != 1:
                continue
            total_gcd1 += 1

            L  = math.lcm(*e_tuple)
            N  = n * L
            safe_pts = enumerate_safe_points(e_tuple, n, L, N)
            x0 = len(safe_pts)
            safe_set = set(safe_pts)

            witnesses  = an_witnesses(n, L)
            safe_wit   = [w for w in witnesses if w in safe_set]
            failed_wit = [w for w in witnesses if w not in safe_set]

            n_safe_wit  = len(safe_wit)
            all_survive = (len(failed_wit) == 0)
            any_survive = (n_safe_wit > 0)

            if all_survive:
                witnesses_all_safe += 1
            elif any_survive:
                witnesses_partial += 1
            else:
                witnesses_none_safe += 1

            sorted_t = tuple(sorted(e_tuple))
            is_an    = int(sorted_t == An_sorted)

            # Classify safe points
            classes = [classify_safe_point(k, n, L, N) for k in safe_pts]

            detail_rows.append({
                "n":                  n,
                "sorted_tuple":       " ".join(map(str, sorted_t)),
                "L":                  L,
                "N":                  N,
                "x0":                 x0,
                "phi_n":              phi_n,
                "is_an":              is_an,
                "n_witnesses":        len(witnesses),
                "n_witnesses_safe":   n_safe_wit,
                "all_witnesses_safe": int(all_survive),
                "safe_point_classes": " | ".join(classes),
            })

            if not all_survive:
                failure_rows.append({
                    "n":               n,
                    "sorted_tuple":    " ".join(map(str, sorted_t)),
                    "L":               L,
                    "N":               N,
                    "x0":              x0,
                    "phi_n":           phi_n,
                    "is_an":           is_an,
                    "n_witnesses_safe": n_safe_wit,
                    "n_witnesses_failed": len(failed_wit),
                    "failed_witnesses": " ".join(map(str, failed_wit)),
                    "all_safe_pts":    " ".join(map(str, safe_pts)),
                    "safe_point_classes": " | ".join(classes),
                })

        summary_rows.append({
            "n":                  n,
            "phi_n":              phi_n,
            "max_e":              max_e,
            "total_gcd1":         total_gcd1,
            "witnesses_all_safe": witnesses_all_safe,
            "witnesses_partial":  witnesses_partial,
            "witnesses_none":     witnesses_none_safe,
            "witnesses_any_fail": total_gcd1 - witnesses_all_safe,
            "pct_all_safe":       100.0 * witnesses_all_safe / total_gcd1 if total_gcd1 else 0.0,
        })

        print(f"  n={n}: phi={phi_n}, total={total_gcd1}, "
              f"all_survive={witnesses_all_safe} ({100*witnesses_all_safe/total_gcd1:.1f}%), "
              f"partial={witnesses_partial}, none={witnesses_none_safe}")

    return summary_rows, failure_rows, detail_rows


def write_outputs(summary_rows, failure_rows, detail_rows):
    all_survive_globally = all(r["witnesses_any_fail"] == 0 for r in summary_rows)

    # Summary markdown
    lines = []
    lines.append("# Safe-Point Witness Survey (v1)")
    lines.append("")
    lines.append("**Question:** For each gcd-1 tuple E, do the A_n witnesses")
    lines.append("k = j*L with gcd(j,n)=1 remain safe (not in any D_e)?")
    lines.append("")
    lines.append("If ALL tuples have all phi(n) witnesses surviving:")
    lines.append("  → Lemma E proved: x_0(E) >= phi(n) for all gcd-1 E  (uniform witnesses).")
    lines.append("")
    lines.append("## Per-n Results")
    lines.append("")
    lines.append("| n | phi(n) | max_e | gcd-1 tuples | all survive | partial | none | % all survive |")
    lines.append("|---:|---:|---:|---:|---:|---:|---:|---:|")
    for r in summary_rows:
        lines.append(
            f"| {r['n']} | {r['phi_n']} | {r['max_e']} | {r['total_gcd1']} | "
            f"{r['witnesses_all_safe']} | {r['witnesses_partial']} | "
            f"{r['witnesses_none']} | {r['pct_all_safe']:.1f}% |"
        )
    lines.append("")
    lines.append("## Global Verdict")
    lines.append("")
    if all_survive_globally:
        lines.append("**RESULT: ALL tuples in all tested grids have ALL A_n witnesses surviving.**")
        lines.append("")
        lines.append("The points k = j*L (gcd(j,n)=1) are UNIVERSALLY SAFE for every gcd-1 tuple E.")
        lines.append("")
        lines.append("### Consequence: Lemma E is proved on this grid")
        lines.append("")
        lines.append("For every tested gcd-1 tuple E:")
        lines.append("  x_0(E) >= #{j in {1,...,n-1} : gcd(j,n)=1} = phi(n) = x_0(A_n)")
        lines.append("")
        lines.append("Combined with Lemma P (x_0(A_n) = phi(n), analytically proved), this gives")
        lines.append("x_0(E) >= phi(n) >= 2 for all n>=3.  Lemma 8.1 follows.")
        lines.append("")
        lines.append("Next step: ANALYTIC PROOF that k=j*L (gcd(j,n)=1) is safe for ALL gcd-1 E.")
        lines.append("This would close Lemma E and the rational SINGLE theorem for all n.")
    else:
        total_fail = sum(r["witnesses_any_fail"] for r in summary_rows)
        lines.append(f"**RESULT: {total_fail} tuples have at least one A_n witness that is NOT safe.**")
        lines.append("")
        lines.append("The k=j*L witnesses do NOT universally generalize.")
        lines.append("See failures CSV for details; look for twisted witnesses or alternative routes.")

    with open(OUT_SUMMARY, "w") as f:
        f.write("\n".join(lines) + "\n")

    # Failure CSV
    with open(OUT_FAILURES, "w", newline="") as f:
        if failure_rows:
            w = csv.DictWriter(f, fieldnames=list(failure_rows[0].keys()))
            w.writeheader()
            w.writerows(failure_rows)
        else:
            f.write("n,note\n")
            f.write("all,No failures: all A_n witnesses survived for all tuples\n")

    # Detail CSV
    with open(OUT_DETAIL, "w", newline="") as f:
        if detail_rows:
            fields = ["n", "sorted_tuple", "L", "N", "x0", "phi_n", "is_an",
                      "n_witnesses", "n_witnesses_safe", "all_witnesses_safe",
                      "safe_point_classes"]
            w = csv.DictWriter(f, fieldnames=fields)
            w.writeheader()
            for row in detail_rows:
                w.writerow({k: row[k] for k in fields})

    print(f"\nOutputs written:")
    print(f"  {OUT_SUMMARY}")
    print(f"  {OUT_FAILURES}")
    print(f"  {OUT_DETAIL}")


def main():
    print("Safe-Point Witness Enumerator v1")
    print("Scanning gcd-1 tuples for n=3..6 ...")
    summary_rows, failure_rows, detail_rows = run_scan()
    write_outputs(summary_rows, failure_rows, detail_rows)
    print("\nDone.")


if __name__ == "__main__":
    main()
