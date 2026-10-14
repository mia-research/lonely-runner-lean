"""Exhaustive: every 7-subset of 1..D, collecting the CRITICAL sets (at most one free flank).

A set with no free flank would refute Existence at order 8. A set with exactly one is the tight case
the proof has to survive, so its shape is what a uniform theorem must handle.
"""
import sys
from itertools import combinations
from math import gcd
def blocked(d, e, k):
    r = (d * (8 * k + 1)) % (8 * e)
    return min(r, 8 * e - r) < e
def free_flanks(D):
    out = []
    for e in D:
        others = [d for d in D if d != e]
        for k in range(e):
            if all(not blocked(d, e, k) for d in others):
                out.append(e); break
    return out
if __name__ == '__main__':
    DMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 26
    tot = 0; none_ = []; one = []
    for sub in combinations(range(1, DMAX + 1), 7):
        tot += 1
        D = list(sub)
        fr = free_flanks(D)
        if len(fr) == 0: none_.append(D)
        elif len(fr) == 1: one.append((D, fr[0]))
    print(f"exhaustive 7-subsets of 1..{DMAX}: {tot} sets")
    print(f"  NO free flank : {len(none_)}   <-- any entry refutes Existence at order 8")
    for D in none_[:10]: print("     COUNTEREXAMPLE", D)
    print(f"  exactly ONE free flank: {len(one)}")
    for D, e in one[:25]:
        g = gcd(D[-1], D[-2]) if len(D) >= 2 else 0
        print(f"     {D}  free only at {e}{'  (= d_max)' if e == max(D) else ''}")
    if len(one) > 25: print(f"     ... {len(one)-25} more")
    if one:
        atmax = sum(1 for D, e in one if e == max(D))
        print(f"  of the one-free sets, the free flank is d_max in {atmax} of {len(one)}")
        from collections import Counter
        print(f"  gcd of the whole set: {Counter(__import__('functools').reduce(gcd, D) for D, e in one)}")
