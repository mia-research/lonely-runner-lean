"""
Check Theorem 5.2-SR2 (Lifted Slot-Residue) on L_residual.

Decompose W := G u pA into:
    W_1 = {w in W : n does-not-divide w}
    W_2 = {w/n : w in W, n divides w}

A joint witness on lattice 1/n^2 at t* = (n*k + c)/n^2 with
    k in {0,...,n-1}, c in {1,...,n-1}
is characterized by:
    (a) For w' in W_2: ||w' c / n|| >= 1/n  (Z2-condition, depends on c only)
    (b) For w  in W_1: ||w (n k + c)/n^2|| >= 1/n  (PCL-style, depends on (k, c))

Goal: empirically verify that every L_residual case admits some (k, c) satisfying (a)+(b).
For each L_residual case, classify by which (c, k) is the FIRST witness on the n^2 lattice.
"""

import csv
import math
from fractions import Fraction

CSV = "/Users/trentpalelei/Desktop/Math Ex/reports/phase6_residual_arithmetic.csv"


def parse_speeds(s: str):
    return [int(x) for x in s.split("-")]


def norm_int(num, den):
    """||num/den|| where num, den integers and den > 0."""
    r = num % den
    return min(r, den - r)


def is_joint_witness(n, G, A, p, t_num, t_den):
    """Check ||v t|| >= 1/n for v in G and ||u {p t}|| >= 1/n for u in A, with t = t_num/t_den."""
    threshold_num = t_den  # we'll compare norm * n >= t_den
    # ||v t|| >= 1/n iff norm_int(v*t_num, t_den) * n >= t_den
    for v in G:
        if norm_int(v * t_num, t_den) * n < t_den:
            return False
    # {p t} = (p t_num mod t_den) / t_den
    pt_num = (p * t_num) % t_den
    for u in A:
        if norm_int(u * pt_num, t_den) * n < t_den:
            return False
    return True


def find_n2_witness(n, G, A, p):
    """Search t = (n*k + c)/n^2 for k in {0,...,n-1}, c in {1,...,n-1}."""
    den = n * n
    witnesses = []
    for c in range(1, n):
        for k in range(n):
            m = n * k + c
            if is_joint_witness(n, G, A, p, m, den):
                witnesses.append((k, c, m))
    return witnesses


def w1_w2_decomposition(n, G, A, p):
    W = list(G) + [p * u for u in A]
    W1 = [w for w in W if w % n != 0]
    W2 = [w // n for w in W if w % n == 0]
    return W, W1, W2


def z2_good_c(n, W2):
    """Return c in {1,...,n-1} with ||w' c / n|| >= 1/n for all w' in W2,
    i.e., w'*c mod n != 0 for all w' in W2."""
    good = []
    for c in range(1, n):
        if all(w * c % n != 0 for w in W2):
            good.append(c)
    return good


def main():
    with open(CSV) as f:
        rows = [r for r in csv.DictReader(f) if r['stratum'] == 'L_residual']

    print(f"L_residual cases: {len(rows)}\n")

    sr_closed = 0
    sr_fail_n2_closed = 0
    sr_fail_n2_fail = 0
    no_z2_good_c = 0
    z2_good_but_no_k = 0

    detailed = []

    for r in rows:
        n = int(r['n'])
        G = parse_speeds(r['G_speeds'])
        A = parse_speeds(r['A_speeds'])
        p = int(r['p'])

        W, W1, W2 = w1_w2_decomposition(n, G, A, p)
        sr_applies = (len(W2) == 0)

        if sr_applies:
            sr_closed += 1
            continue

        # SR fails: try n^2 lattice
        witnesses = find_n2_witness(n, G, A, p)
        z2_good = z2_good_c(n, W2)

        if witnesses:
            sr_fail_n2_closed += 1
            # also report which (k,c)
            first_k, first_c, first_m = witnesses[0]
            detailed.append({
                'n': n, 'G': G, 'A': A, 'p': p,
                'W2': W2, 'z2_good_c': z2_good,
                'witness_kcm': (first_k, first_c, first_m),
                'n_witnesses': len(witnesses),
                'first_c_in_z2_good': first_c in z2_good,
            })
        else:
            sr_fail_n2_fail += 1
            print(f"  ALERT: no n^2 witness for n={n}, G={G}, A={A}, p={p}, W2={W2}, z2_good_c={z2_good}")

    print(f"SR closed:                  {sr_closed}/53")
    print(f"SR failed + n^2 witness:    {sr_fail_n2_closed}/53")
    print(f"SR failed + no n^2 witness: {sr_fail_n2_fail}/53")
    print()

    # Structural pattern analysis
    consistent_c_in_z2 = sum(1 for d in detailed if d['first_c_in_z2_good'])
    print(f"Of {len(detailed)} SR-failure cases with n^2 witness:")
    print(f"  Witness c lies in Z2-good set: {consistent_c_in_z2}/{len(detailed)}")
    print()

    # Detail per case
    print("First witness (k, c) per SR-failure case:")
    print(f"  {'n':>2} {'G':<14} {'A':<10} {'p':>2} {'W2':<14} {'Z2-good c':<14} {'witness (k,c)':<14} {'in Z2?':<8}")
    for d in detailed:
        k, c, m = d['witness_kcm']
        print(f"  {d['n']:>2} {str(d['G']):<14} {str(d['A']):<10} {d['p']:>2} {str(d['W2']):<14} "
              f"{str(d['z2_good_c']):<14} ({k},{c}) m={m:<5} {'YES' if d['first_c_in_z2_good'] else 'NO':<8}")


if __name__ == "__main__":
    main()
