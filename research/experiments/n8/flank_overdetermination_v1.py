"""Is shadowing every flank at once impossible? Exhaustive search, exact integer arithmetic.

Blocked test without fractions: the runner at difference d is in the way at opening k of flank e iff
circDist((d/e)(k + 1/8)) < 1/8. Writing the phase as d(8k+1)/(8e), that is
    r = d(8k+1) mod 8e,   blocked  <=>  min(r, 8e - r) < e.

For every 7-subset of {1..D} (the differences of one subject at order 8) we ask whether some flank is
FREE -- some opening of it at which all six other differences are clear. A set with NO free flank would
be a counterexample to Existence at order 8 (via lonely_iff_exists_flank).

Also recorded: the divisibility signature of the hardest sets -- max_j gcd(d_j, e) at each shadowed
flank -- to test whether shadowing always demands a difference sharing a large factor with the flank.
"""
import sys
from itertools import combinations
from math import gcd
def blocked(d, e, k):
    r = (d * (8 * k + 1)) % (8 * e)
    return min(r, 8 * e - r) < e
def free_openings(D, e):
    others = [d for d in D if d != e]
    return [k for k in range(e) if all(not blocked(d, e, k) for d in others)]
def n_free_flanks(D, stop_at_one=True):
    n = 0
    for e in D:
        if free_openings(D, e):
            n += 1
            if stop_at_one: return n
    return n
if __name__ == '__main__':
    DMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 22
    print(f"exhaustive over 7-subsets of 1..{DMAX} (order 8, integer differences)")
    tot = 0; nofree = []; minfree = 99; mins = []
    for sub in combinations(range(1, DMAX + 1), 7):
        tot += 1
        D = list(sub)
        cnt = 0; frees = []
        for e in D:
            if free_openings(D, e): cnt += 1; frees.append(e)
        if cnt == 0: nofree.append(D)
        if cnt < minfree:
            minfree = cnt; mins = [(D, frees)]
        elif cnt == minfree and len(mins) < 8:
            mins.append((D, frees))
    print(f"  sets: {tot}")
    print(f"  sets with NO free flank: {len(nofree)}")
    if nofree:
        for D in nofree[:10]: print("    COUNTEREXAMPLE:", D)
    print(f"  fewest free flanks: {minfree}")
    for D, fr in mins[:8]:
        print(f"    {D} -> free flanks {fr}")
    print()
    print("  divisibility signature of the hardest sets (shadowed flanks only):")
    for D, fr in mins[:4]:
        for e in D:
            if e in fr: continue
            g = max(gcd(d, e) for d in D if d != e)
            print(f"    set {D}  flank {e:3}: max gcd(d_j, e) = {g}, so min denominator c = {e // g}")
