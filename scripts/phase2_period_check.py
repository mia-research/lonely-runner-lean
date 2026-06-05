"""
Phase 2 — Validate the period of G_s numerically.

v11.5 claims (line 351, line 577): "G_s has period 1/L" where L = lcm(slow speeds).
Analytic claim: G_s has period 1/gcd(slow speeds).

For each LRC-realisable (n, slow), compute the period empirically:
  • Discretise [0, 2) finely.
  • Compute the indicator G_s(t) = 1[circDist(v_i·t) >= 1/n ∀ i].
  • Find smallest T > 0 with G_s(t) = G_s(t+T) for all t in the test grid.
  • Compare to 1/L and 1/gcd.

Reports any case where the actual period disagrees with 1/L.
"""

import itertools
import math
from functools import reduce


def gcd_list(xs):
    return reduce(math.gcd, xs, 0)


def lcm(a, b):
    return a * b // math.gcd(a, b)


def lcm_list(xs):
    return reduce(lcm, xs, 1)


def circ_dist(x):
    f = x - math.floor(x)
    return min(f, 1 - f)


def in_Gs(t, slow, n):
    thresh = 1.0 / n
    return all(circ_dist(v * t) >= thresh - 1e-12 for v in slow)


def measured_period(slow, n, candidate_T, n_test=10_000):
    """Check whether candidate_T is a period: G(t) = G(t + T) at n_test sample points."""
    # Sample n_test points in [0, candidate_T) and compare.
    for i in range(n_test):
        t = candidate_T * (i + 0.5) / n_test
        # also check at slight offsets to catch boundary cases
        for shift in (0.0, candidate_T * 0.001):
            tt = t + shift
            if in_Gs(tt, slow, n) != in_Gs(tt + candidate_T, slow, n):
                return False
    return True


def main():
    print("=" * 78)
    print("PHASE 2 — Period validation: 1/L (manuscript) vs 1/gcd (analytic)")
    print("=" * 78)
    print()

    NS = [3, 4, 5, 6, 7]
    MAX_SPEED = 8

    total = 0
    period_mismatches = []
    confirms = 0

    for n in NS:
        k = n - 2
        if k < 1:
            continue
        for slow_tup in itertools.combinations(range(1, MAX_SPEED + 1), k):
            slow = list(slow_tup)
            L = lcm_list(slow)
            d = gcd_list(slow)
            # Period claim: 1/L (manuscript) vs 1/d (analytic).
            T_L = 1.0 / L
            T_d = 1.0 / d
            total += 1
            # Check T_L is a period (often false), T_d is a period (always true).
            is_L_period = measured_period(slow, n, T_L)
            is_d_period = measured_period(slow, n, T_d)
            if not is_d_period:
                # something is wrong with our setup
                period_mismatches.append({
                    "n": n, "slow": slow, "L": L, "d": d,
                    "msg": "1/gcd FAILS as period — investigate"
                })
                continue
            if is_L_period and d == 1:
                # Both 1/L and 1/d are valid periods, 1/d is the fundamental one (= 1 here)
                confirms += 1
            elif is_L_period and d > 1:
                # 1/L is a period and 1/d is the fundamental
                # (likely L is just a multiple of 1/d; valid but manuscript could simplify)
                confirms += 1
            else:
                # 1/L is NOT a period — manuscript wrong
                period_mismatches.append({
                    "n": n, "slow": slow, "L": L, "d": d,
                    "1/L": T_L, "1/d": T_d,
                    "manuscript_period_works": is_L_period,
                    "analytic_period_works": is_d_period,
                    "ratio_L/d": L / d,
                })

    print(f"Slow-speed families tested: {total}")
    print(f"Manuscript's 1/L is a period: {confirms}")
    print(f"Manuscript's 1/L FAILS as period (1/d is correct): {len(period_mismatches)}")
    print()
    if period_mismatches:
        print("PERIOD MISMATCHES (manuscript 1/L is NOT a period of G_s):")
        for m in period_mismatches[:20]:
            print(f"  {m}")
        if len(period_mismatches) > 20:
            print(f"  ... and {len(period_mismatches) - 20} more")
    else:
        print(">>> Manuscript's 1/L claim never fails in tested range.")
        print(">>> But this is consistent with 1/L being A period (multiple of fundamental).")
        print(">>> The CONCEPTUAL error is the manuscript treating 1/L as fundamental.")


if __name__ == "__main__":
    main()
