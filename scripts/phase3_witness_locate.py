"""
Phase 3 — Locate the actual witnesses for the §10.1 conclusion in
known counterexamples to joint_fine_cell_exists.

Uses EXACT rational interval arithmetic (boundary-aware).

For each LRC-counterexample (G_speeds, A_speeds, p) where joint_fine_cell_exists
returns 0, compute the joint good set
  G_joint = ⋂_{v ∈ G_speeds ∪ {p·v : v ∈ A_speeds}}  {t ∈ [0,1) : ||v·t|| >= 1/n}
exactly. Report:
  - Is the joint set non-empty? (Phase 1 says yes; this re-confirms.)
  - Width of largest interval (if 0, all witnesses are BOUNDARY POINTS)
  - The witnesses themselves
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


def isprime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    i = 3
    while i * i <= n:
        if n % i == 0:
            return False
        i += 2
    return True


def good_cell_idx(speeds, n, L):
    result = []
    for m in range(n * L):
        ok = True
        for v in speeds:
            d = L // v
            r = (m // d) % n
            if not (1 <= r <= n - 2):
                ok = False
                break
        if ok:
            result.append(m)
    return result


def good_intervals(v, n):
    """List of closed (a, b) intervals on [0, 1) where ||v·t|| >= 1/n."""
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
    print("PHASE 3 — Exact witness localisation for joint_fine_cell counterexamples")
    print("=" * 78)
    print()

    SPEED_POOL = list(range(1, 9))
    PRIMES = [p for p in range(2, 20) if isprime(p)]
    NS = [3, 4, 5, 6, 7]

    counterexamples = []
    for n in NS:
        for kG in [1, 2, 3]:
            for G_speeds_tup in itertools.combinations(SPEED_POOL, kG):
                G_speeds = list(G_speeds_tup)
                L_G = lcm_list(G_speeds)
                G_idx = good_cell_idx(G_speeds, n, L_G)
                if not G_idx:
                    continue
                for kA in [1, 2]:
                    for A_speeds_tup in itertools.combinations(SPEED_POOL, kA):
                        A_speeds = list(A_speeds_tup)
                        if set(G_speeds) & set(A_speeds):
                            continue
                        L_A = lcm_list(A_speeds)
                        A_idx = good_cell_idx(A_speeds, n, L_A)
                        if not A_idx:
                            continue
                        for p in PRIMES:
                            if math.gcd(p, L_G) != 1:
                                continue
                            if p in G_speeds or p in A_speeds:
                                continue
                            if not (p < n * L_G):
                                continue
                            M = n * L_G * L_A * p
                            if M > 5_000_000:
                                continue
                            g_all = math.gcd(p, reduce(math.gcd, G_speeds + A_speeds, 0))
                            if g_all != 1:
                                continue
                            joint = 0
                            for mpp in range(M):
                                alpha = mpp // (L_A * p)
                                beta = (mpp % (n * L_G * L_A)) // L_G
                                if alpha in set(G_idx) and beta in set(A_idx):
                                    joint += 1
                                    break
                            if joint == 0:
                                counterexamples.append((n, G_speeds, A_speeds, p))

    print(f"Counterexamples to enumerate: {len(counterexamples)}")
    print()

    # Witness analysis
    nonempty = 0
    truly_empty = 0
    all_zero_width = 0  # all witnesses are boundary points
    some_positive_width = 0  # some witnesses are in open intervals
    width_histogram = Counter()  # bucket widths
    examples_zero = []
    examples_pos = []

    for n, G_speeds, A_speeds, p in counterexamples:
        # LRC reduction: joint speeds = G ∪ {p*v_A : v_A in A}
        joint_speeds = list(G_speeds) + [p * v for v in A_speeds]
        intervals = joint_good_intervals(joint_speeds, n)
        if not intervals:
            truly_empty += 1
            continue
        nonempty += 1
        max_width = max(b - a for a, b in intervals)
        if max_width == 0:
            all_zero_width += 1
            if len(examples_zero) < 8:
                examples_zero.append((n, G_speeds, A_speeds, p, joint_speeds, intervals))
        else:
            some_positive_width += 1
            if len(examples_pos) < 8:
                examples_pos.append((n, G_speeds, A_speeds, p, joint_speeds, intervals, max_width))

        # Bucket widths
        if max_width == 0:
            width_histogram["0 (boundary only)"] += 1
        else:
            # Categorise by magnitude
            log_w = math.log10(float(max_width))
            bucket = f"10^{int(math.floor(log_w))}"
            width_histogram[bucket] += 1

    print(f"Joint good set non-empty: {nonempty}")
    print(f"Joint good set TRULY EMPTY: {truly_empty}  (would be LRC violations!)")
    print()
    print(f"Of the non-empty:")
    print(f"  ALL witnesses are boundary points (max width 0): {all_zero_width}")
    print(f"  Some witnesses in open intervals (max width > 0): {some_positive_width}")
    print()
    print(f"Width histogram of max-width interval (across all non-empty counterexamples):")
    for bucket, count in sorted(width_histogram.items()):
        print(f"  {bucket}: {count}")
    print()
    if examples_zero:
        print(f"Examples with ALL boundary witnesses (max width 0):")
        for n, G, A, p, joint_speeds, intervals in examples_zero:
            print(f"  n={n} G={G} A={A} p={p} joint_speeds={joint_speeds}")
            print(f"    witnesses (single points): {[(str(a), str(b)) for a, b in intervals]}")
    if examples_pos:
        print()
        print(f"Examples with positive-width witness intervals:")
        for n, G, A, p, joint_speeds, intervals, max_w in examples_pos:
            print(f"  n={n} G={G} A={A} p={p} joint_speeds={joint_speeds} max_width={max_w}")
            print(f"    first interval: [{intervals[0][0]}, {intervals[0][1]}]")


if __name__ == "__main__":
    main()
