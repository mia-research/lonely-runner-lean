"""The near-AP extremal {2,3,4,5,6,7,16}: is it isolated, or the first of a family?

Exhaustive search over 7-subsets of {1..30} found exactly ONE set with a single free flank:
six consecutive integers plus an outlier. This probes that shape directly, well past d_max = 30:
consecutive blocks a..a+5 with an outlier N, and the structure of the critical set's own free flank.
"""
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
                out.append((e, k)); break
    return out
print("(1) the critical set itself")
D = [2,3,4,5,6,7,16]
fr = free_flanks(D)
print(f"    {D}: free flanks (with first free opening) {fr}")
for e in D:
    others = [d for d in D if d != e]
    ks = [k for k in range(e) if all(not blocked(d, e, k) for d in others)]
    print(f"      flank {e:3}: {len(ks)} free opening(s) {ks[:6]}")
print()
print("(2) the family {2,3,4,5,6,7,N}: how many flanks are free?")
zero = []; one = []
for N in range(8, 2001):
    if N in (2,3,4,5,6,7): continue
    D = sorted([2,3,4,5,6,7,N])
    f = free_flanks(D)
    if len(f) == 0: zero.append(N)
    elif len(f) == 1: one.append((N, f[0]))
print(f"    N from 8 to 2000: zero free flanks -> {zero if zero else 'NONE'}")
print(f"    exactly one free flank -> {[(n,e) for n,(e,k) in one]}")
print()
print("(3) other consecutive blocks a..a+5 plus an outlier N (a <= 12, N <= 600)")
zero2 = []; one2 = []
for a in range(1, 13):
    blk = list(range(a, a+6))
    for N in range(a+6, 601):
        D = sorted(blk + [N])
        if len(set(D)) != 7: continue
        f = free_flanks(D)
        if len(f) == 0: zero2.append(D)
        elif len(f) == 1: one2.append((D, f[0]))
print(f"    zero free flanks: {zero2 if zero2 else 'NONE'}")
print(f"    exactly one free flank: {len(one2)} sets")
for D, f in one2[:12]: print(f"      {D} -> free only at flank {f[0]} (opening k={f[1]})")
if len(one2) > 12: print(f"      ... {len(one2)-12} more")
print()
print("(4) are the one-free sets scalings of each other?")
for D, f in one2[:12]:
    g = 0
    for d in D: g = gcd(g, d)
    print(f"      {D}: gcd {g}, reduced {[d//g for d in D]}")
