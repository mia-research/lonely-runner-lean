"""
Phase 1 — confirm the §10.1 / §11.1 conclusion holds on LRC-realisable inputs.

Uses exact rational interval arithmetic (no grid scan) to check whether
the joint good set is non-empty on [0, 1).

For each strict-LRC-shape (n, slow speeds, V) in DI/ModDI hard case, compute
the joint good set
  G_joint = ⋂_{v ∈ slow ∪ {V}}  {t ∈ [0, 1) : ‖v·t‖ ≥ 1/n}
as a union of intervals (rational endpoints), and report whether non-empty.
"""

import itertools
import math
from functools import reduce
from fractions import Fraction


def gcd_list(xs):
    return reduce(math.gcd, xs, 0)


def lcm(a, b):
    return a * b // math.gcd(a, b)


def lcm_list(xs):
    return reduce(lcm, xs, 1)


def largest_prime_factor(n):
    p = 2
    last = None
    while p * p <= n:
        while n % p == 0:
            last = p
            n //= p
        p += 1
    if n > 1:
        last = n
    return last


def good_intervals(v, n):
    """Return list of (a, b) closed intervals (Fractions) on [0, 1) where
    circDist(v·t) >= 1/n. There are v such intervals, each of width (n-2)/(nv)."""
    intervals = []
    for k in range(v):
        a = Fraction(k, v) + Fraction(1, n * v)
        b = Fraction(k, v) + Fraction(n - 1, n * v)
        intervals.append((a, b))
    return intervals


def intersect_unions(U1, U2):
    """Intersect two unions-of-intervals. Each is a sorted list of (a, b)
    disjoint closed intervals. Returns sorted list of (a, b)."""
    result = []
    i = j = 0
    while i < len(U1) and j < len(U2):
        a1, b1 = U1[i]
        a2, b2 = U2[j]
        lo = max(a1, a2)
        hi = min(b1, b2)
        if lo <= hi:
            result.append((lo, hi))
        if b1 < b2:
            i += 1
        else:
            j += 1
    return result


def joint_good_intervals(speeds, n):
    """Intersection of good intervals for all speeds. Sorted disjoint list."""
    if not speeds:
        return [(Fraction(0), Fraction(1))]
    joint = good_intervals(speeds[0], n)
    for v in speeds[1:]:
        joint = intersect_unions(joint, good_intervals(v, n))
        if not joint:
            return []
    return joint


def main():
    print("=" * 78)
    print("PHASE 1 — Conclusion check on strict-LRC-shape inputs (DI/ModDI hard case)")
    print("=" * 78)
    print()
    print("Method: exact rational interval intersection on [0, 1).")
    print()

    NS = [3, 4, 5, 6, 7]
    MAX_SPEED = 10  # cap for slow speeds

    total = 0
    di_hits = 0
    moddi_hits = 0
    overlaps = 0
    conclusion_failures = []
    sample_witnesses = []

    for n in NS:
        k = n - 2
        if k < 1:
            continue
        for slow_tup in itertools.combinations(range(1, MAX_SPEED + 1), k):
            slow = list(slow_tup)
            v_min, v_max = slow[0], slow[-1]
            L = lcm_list(slow)
            for V in range((n - 1) * v_min + 1, (n - 1) * v_max + 1):
                if V in slow:
                    continue
                speeds_all = slow + [V]
                if gcd_list(speeds_all) != 1:
                    continue
                p = largest_prime_factor(V)
                if p is None:
                    continue
                is_di = (math.gcd(p, L) == 1)
                is_moddi = any(s % p == 0 for s in slow)
                if not (is_di or is_moddi):
                    continue
                total += 1
                if is_di:
                    di_hits += 1
                if is_moddi:
                    moddi_hits += 1
                if is_di and is_moddi:
                    overlaps += 1
                # Check conclusion: joint good set non-empty?
                joint = joint_good_intervals(speeds_all, n)
                if not joint:
                    conclusion_failures.append({
                        "n": n, "slow": slow, "V": V, "p": p,
                        "is_DI": is_di, "is_ModDI": is_moddi,
                    })
                elif len(sample_witnesses) < 10:
                    a, b = joint[0]
                    sample_witnesses.append({
                        "n": n, "slow": slow, "V": V, "p": p,
                        "1st_interval": (a, b),
                        "centre": (a + b) / 2,
                        "width": b - a,
                    })

    print(f"Inputs tested:    {total}")
    print(f"  DI-classified:    {di_hits}")
    print(f"  ModDI-classified: {moddi_hits}")
    print(f"  (overlap: {overlaps})")
    print()
    print(f"Conclusion failures (joint good set empty): {len(conclusion_failures)}")
    print()
    if conclusion_failures:
        print("FAILURES:")
        for fail in conclusion_failures[:30]:
            print(f"  {fail}")
        if len(conclusion_failures) > 30:
            print(f"  ... and {len(conclusion_failures) - 30} more")
        print()
        print("Failure rate by n:")
        from collections import Counter
        c = Counter((f["n"]) for f in conclusion_failures)
        for n in NS:
            print(f"  n={n}: {c.get(n, 0)} failures")
    else:
        print(">>> NO FAILURES — joint good set is non-empty for every tested input.")
        print(">>> The CONCLUSION of theorem101_DI / theorem111_ModDI is empirically sound.")
        print(">>> Only the PROOF strategy (Thm 5.2 / joint_fine_cell) is broken.")

    if sample_witnesses:
        print()
        print("Sample witness intervals (first ones):")
        for w in sample_witnesses:
            a, b = w["1st_interval"]
            print(f"  n={w['n']} slow={w['slow']} V={w['V']} p={w['p']} "
                  f"first interval: [{a}, {b}] width={w['width']} centre={w['centre']}")


if __name__ == "__main__":
    main()
