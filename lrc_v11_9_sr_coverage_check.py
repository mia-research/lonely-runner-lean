"""
Theorem 5.2-SR (Slot-Residue Closure) coverage check on L_residual.

Claim: For LRC-shape (n, G, A, p) with gcd(p, L_G) = 1 and W := G u pA,
       if n does-not-divide w for all w in W, then for every s in {1,...,n-1}
       with gcd(s, n) = 1, t* = s/n is a joint witness:
           ||v t*|| >= 1/n  for all v in G
           ||u {p t*}|| >= 1/n  for all u in A

Compare against PCL (gcd(p,n)=1 + n-nmid-v + n-nmid-u, witness t* = 1/n).

Also: empirically verify SR by direct evaluation.
"""

import csv
import math
from fractions import Fraction
from collections import Counter

CSV = "/Users/trentpalelei/Desktop/Math Ex/reports/phase6_residual_arithmetic.csv"


def parse_speeds(s: str):
    # "1-3" -> [1, 3]; "4" -> [4]; "2-5-7" -> [2, 5, 7]
    return [int(x) for x in s.split("-")]


def frac_norm(num, den):
    # ||num/den|| = min(r/den, 1 - r/den) where r = num mod den
    r = num % den
    return min(r, den - r) / den


def pcl_hypotheses(n, G, A, p):
    """gcd(p,n)=1, n nmid v for v in G, n nmid u for u in A."""
    if math.gcd(p, n) != 1:
        return False
    if any(v % n == 0 for v in G):
        return False
    if any(u % n == 0 for u in A):
        return False
    return True


def sr_hypotheses(n, G, A, p):
    """n nmid w for all w in W = G u pA."""
    W = list(G) + [p * u for u in A]
    return all(w % n != 0 for w in W)


def verify_witness(n, G, A, p, t_num, t_den):
    """Verify ||v t|| >= 1/n for v in G AND ||u {p t}|| >= 1/n for u in A.
    t = t_num/t_den exact. Returns (ok, witness_failing_speed_or_none).
    """
    # ||v t|| >= 1/n iff ||v t_num/t_den|| >= 1/n
    threshold = Fraction(1, n)
    for v in G:
        # v * t = v*t_num / t_den. fractional part: (v*t_num mod t_den) / t_den
        num = (v * t_num) % t_den
        # ||x|| = min(num/t_den, 1 - num/t_den)
        norm = min(Fraction(num, t_den), 1 - Fraction(num, t_den))
        if norm < threshold:
            return False, ('G', v, norm)
    # {p t} = (p * t_num mod t_den) / t_den
    pt_num = (p * t_num) % t_den
    for u in A:
        # ||u * pt|| where pt = pt_num/t_den
        num = (u * pt_num) % t_den
        norm = min(Fraction(num, t_den), 1 - Fraction(num, t_den))
        if norm < threshold:
            return False, ('A', u, norm)
    return True, None


def find_sr_witness(n, G, A, p):
    """Return first s in {1,...,n-1} with gcd(s,n)=1 giving a joint witness,
    or None if none works (should not happen if SR hypothesis holds).
    """
    for s in range(1, n):
        if math.gcd(s, n) != 1:
            continue
        ok, _ = verify_witness(n, G, A, p, s, n)
        if ok:
            return s
    return None


def main():
    with open(CSV) as f:
        rows = [r for r in csv.DictReader(f) if r['stratum'] == 'L_residual']

    print(f"Total L_residual cases: {len(rows)}\n")

    pcl_yes = 0
    sr_yes = 0
    sr_verified_yes = 0
    sr_consistency_fail = []  # SR hypothesis holds but no s works (should be empty)
    sr_pcl_diff = []  # cases where SR holds but PCL fails

    by_n = Counter()
    by_n_pcl = Counter()
    by_n_sr = Counter()

    pcl_witness_check_fail = []  # cases where PCL hypothesis holds but t*=1/n fails (should be empty)

    not_closed_by_sr = []  # cases where SR hypothesis fails

    for r in rows:
        n = int(r['n'])
        G = tuple(parse_speeds(r['G_speeds']))
        A = tuple(parse_speeds(r['A_speeds']))
        p = int(r['p'])
        by_n[n] += 1

        pcl_ok = pcl_hypotheses(n, G, A, p)
        sr_ok = sr_hypotheses(n, G, A, p)

        # Direct verification of PCL witness when PCL hypotheses hold
        if pcl_ok:
            ok, fail = verify_witness(n, G, A, p, 1, n)
            if not ok:
                pcl_witness_check_fail.append((n, G, A, p, fail))
            pcl_yes += 1
            by_n_pcl[n] += 1

        # Direct verification of SR
        if sr_ok:
            s = find_sr_witness(n, G, A, p)
            if s is None:
                sr_consistency_fail.append((n, G, A, p))
            else:
                sr_verified_yes += 1
            sr_yes += 1
            by_n_sr[n] += 1
            if not pcl_ok:
                sr_pcl_diff.append((n, G, A, p, s))
        else:
            not_closed_by_sr.append((n, G, A, p))

    print(f"PCL coverage (gcd(p,n)=1, n-nmid-v, n-nmid-u): {pcl_yes}/{len(rows)} = {pcl_yes/len(rows):.1%}")
    print(f"SR coverage  (n-nmid-w for w in W=G u pA):    {sr_yes}/{len(rows)} = {sr_yes/len(rows):.1%}")
    print(f"SR direct-verified (s in (Z/n)^x works):       {sr_verified_yes}/{sr_yes}")
    print(f"SR consistency failures (hyp holds, no witness): {len(sr_consistency_fail)} (should be 0)")
    print(f"PCL witness check failures (hyp holds, t=1/n fails): {len(pcl_witness_check_fail)} (should be 0)")
    print()

    print("Breakdown by n:")
    for n in sorted(by_n):
        print(f"  n={n}: total={by_n[n]}, PCL={by_n_pcl[n]}, SR={by_n_sr[n]}")
    print()

    print(f"Cases SR closes but PCL does NOT: {len(sr_pcl_diff)}")
    for n, G, A, p, s in sr_pcl_diff:
        print(f"  n={n}, G={list(G)}, A={list(A)}, p={p}, gcd(p,n)={math.gcd(p,n)}, witness s={s}/n")

    print()
    print(f"Cases SR does NOT close: {len(not_closed_by_sr)}")
    for n, G, A, p in not_closed_by_sr[:25]:
        W = list(G) + [p * u for u in A]
        bad = [w for w in W if w % n == 0]
        print(f"  n={n}, G={list(G)}, A={list(A)}, p={p}, W={W}, bad-w (multiples of n)={bad}")
    if len(not_closed_by_sr) > 25:
        print(f"  ... +{len(not_closed_by_sr)-25} more")

    # Sanity: SR consistency failures (should never trigger)
    if sr_consistency_fail:
        print("\nSR CONSISTENCY FAILURES (BUG IN CLAIM):")
        for c in sr_consistency_fail:
            print(c)

    if pcl_witness_check_fail:
        print("\nPCL WITNESS CHECK FAILURES (BUG IN CLAIM):")
        for c in pcl_witness_check_fail:
            print(c)


if __name__ == "__main__":
    main()
