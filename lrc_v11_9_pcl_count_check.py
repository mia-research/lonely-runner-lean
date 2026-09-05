"""
For each L_residual case with SR-failure, compute:
  - For each Z2-good c, the set of bad k in {0,...,n-1} for W1 at offset c
  - Verify there exists Z2-good c with bad-k != {0,...,n-1}

This validates the structural form of Theorem 5.2-SR2.

Companion: lrc_v11_9_n2_lattice_check.py
"""

import csv
import math
from collections import defaultdict

CSV = "/Users/trentpalelei/Desktop/Math Ex/reports/phase6_residual_arithmetic.csv"


def parse_speeds(s: str):
    return [int(x) for x in s.split("-")]


def norm_int(num, den):
    r = num % den
    return min(r, den - r)


def z2_good(n, W2):
    return [c for c in range(1, n) if all((w * c) % n != 0 for w in W2)]


def bad_k_for_w1(n, W1, c):
    """For each w in W1, find k in {0,...,n-1} with ||w(nk+c)/n^2|| < 1/n.
    Return union of bad k across all w.
    """
    bad = set()
    n2 = n * n
    for w in W1:
        for k in range(n):
            m = n * k + c
            if norm_int(w * m, n2) * n < n2:
                bad.add(k)
    return bad


def main():
    with open(CSV) as f:
        rows = [r for r in csv.DictReader(f) if r['stratum'] == 'L_residual']

    sr_failure_cases = []
    for r in rows:
        n = int(r['n'])
        G = parse_speeds(r['G_speeds'])
        A = parse_speeds(r['A_speeds'])
        p = int(r['p'])
        W = list(G) + [p * u for u in A]
        W2 = [w // n for w in W if w % n == 0]
        if W2:
            W1 = [w for w in W if w % n != 0]
            sr_failure_cases.append((n, G, A, p, W1, W2))

    print(f"SR-failure cases: {len(sr_failure_cases)}\n")
    print(f"{'n':>2} {'G':<14} {'A':<10} {'p':>2} |W1| |W2|  {'Z2-good':<14} "
          f"{'good c with bad-k != {0..n-1}'}")

    all_succeed = 0
    failures = []

    for (n, G, A, p, W1, W2) in sr_failure_cases:
        Z2 = z2_good(n, W2)
        eligible = []
        for c in Z2:
            bad = bad_k_for_w1(n, W1, c)
            good_ks = [k for k in range(n) if k not in bad]
            if good_ks:
                eligible.append((c, len(bad), good_ks))

        if eligible:
            all_succeed += 1
            # Choose best c (lowest bad-k count)
            eligible.sort(key=lambda x: x[1])
            best_c, badct, good_ks = eligible[0]
            print(f"{n:>2} {str(G):<14} {str(A):<10} {p:>2}  {len(W1):>2}  {len(W2):>2}  "
                  f"{str(Z2):<14}  best c={best_c} bad-k={badct} good k∈{good_ks}")
        else:
            failures.append((n, G, A, p, W1, W2, Z2))

    print()
    print(f"Cases where some Z2-good c has bad-k != all of {{0..n-1}}: {all_succeed}/{len(sr_failure_cases)}")
    if failures:
        print(f"\nFailures (should be 0):")
        for f in failures:
            print(" ", f)


if __name__ == "__main__":
    main()
