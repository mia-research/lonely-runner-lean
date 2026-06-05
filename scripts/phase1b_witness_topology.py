"""
Phase 1b — How many LRC-realisable inputs have ONLY boundary-point witnesses?

For each strict-LRC-shape input from Phase 1, classify the joint good set:
  - "open" (max interval width > 0) — fine-cell proofs CAN find witnesses
  - "boundary-only" (max width = 0, but non-empty) — fine-cell proofs CANNOT
  - "empty" — LRC violation (shouldn't happen)

If "boundary-only" count is non-trivial in the DI/ModDI hard case, then the
fine-cell approach is fundamentally inadequate even with maximally tight
hypotheses. The fix must be a different proof strategy, not just a tighter lemma.
"""

import itertools
import math
from functools import reduce
from fractions import Fraction
from collections import Counter


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
    intervals = []
    for k in range(v):
        a = Fraction(k, v) + Fraction(1, n * v)
        b = Fraction(k, v) + Fraction(n - 1, n * v)
        intervals.append((a, b))
    return intervals


def intersect_unions(U1, U2):
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
    print("PHASE 1b — Witness topology on strict-LRC-shape inputs")
    print("=" * 78)
    print()

    NS = [3, 4, 5, 6, 7]
    MAX_SPEED = 10

    counts_di = Counter()
    counts_moddi = Counter()
    boundary_examples_di = []
    boundary_examples_moddi = []
    total_di = 0
    total_moddi = 0

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
                ints = joint_good_intervals(speeds_all, n)
                if not ints:
                    cls = "empty"
                else:
                    max_w = max(b - a for a, b in ints)
                    cls = "open" if max_w > 0 else "boundary-only"
                if is_di:
                    counts_di[cls] += 1
                    total_di += 1
                    if cls == "boundary-only" and len(boundary_examples_di) < 8:
                        boundary_examples_di.append((n, slow, V, p, ints))
                if is_moddi:
                    counts_moddi[cls] += 1
                    total_moddi += 1
                    if cls == "boundary-only" and len(boundary_examples_moddi) < 8:
                        boundary_examples_moddi.append((n, slow, V, p, ints))

    print(f"DI-classified inputs:    {total_di}")
    for cls in ["open", "boundary-only", "empty"]:
        c = counts_di[cls]
        pct = 100 * c / max(1, total_di)
        print(f"  {cls}: {c}  ({pct:.1f}%)")
    print()
    print(f"ModDI-classified inputs: {total_moddi}")
    for cls in ["open", "boundary-only", "empty"]:
        c = counts_moddi[cls]
        pct = 100 * c / max(1, total_moddi)
        print(f"  {cls}: {c}  ({pct:.1f}%)")
    print()
    if boundary_examples_di:
        print("DI boundary-only examples:")
        for n, slow, V, p, ints in boundary_examples_di:
            print(f"  n={n} slow={slow} V={V} p={p} witnesses: {[(str(a), str(b)) for a, b in ints]}")
    print()
    if boundary_examples_moddi:
        print("ModDI boundary-only examples:")
        for n, slow, V, p, ints in boundary_examples_moddi:
            print(f"  n={n} slow={slow} V={V} p={p} witnesses: {[(str(a), str(b)) for a, b in ints]}")


if __name__ == "__main__":
    main()
