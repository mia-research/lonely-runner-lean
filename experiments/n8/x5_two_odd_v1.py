#!/usr/bin/env python3
"""Decide the x=5 sector of Lemma 7 at k=7, p=163, exhaustively.

x = number of speeds in T with 8 | v.  The gcd side condition forces at least two
speeds of T to be odd, so x <= 5, and x = 5 means T = {5 coarse} u {2 odd}.

From max_union_v1: five dilates of the 41-arc leave at least U_min(5) = 12 of the
163 residue classes mod 163 entirely uncovered.  From two_adic_blocks_v1: an odd
speed covers at most 2 of the 4 targets in any class.  So the two odd speeds must
between them cover all 4 targets of every class the coarse speeds miss.

Let D(v1,v2) = { r : S_v1(r) u S_v2(r) = {0,1,2,3} }.  A bad cover with x = 5
exists iff some odd pair has complement(D) coverable by 5 coarse dilates -- which
requires |D| >= 12 as a first filter.  This enumerates all C(324,2) = 52326 pairs.
"""
from itertools import combinations

N, H, p = 1304, 652, 163

def covers(j, v):
    r = (j * v) % N
    return r < p or r > N - p

odd = [v for v in range(1, H + 1) if v % 2 == 1 and v % p != 0]
coarse_w = list(range(1, H // 8 + 1))          # v = 8w, w = 1..81

# B[v][t] = bitmask over r in 1..163 of classes where target r+163t is covered
B = {}
for v in odd:
    bs = [0, 0, 0, 0]
    for i, r in enumerate(range(1, p + 1)):
        for t in range(4):
            if covers(r + p * t, v):
                bs[t] |= 1 << i
    B[v] = bs

# coarse dilate masks over the same class indexing
CM = {}
for w in coarse_w:
    m = 0
    for i, r in enumerate(range(1, p + 1)):
        if covers(r, 8 * w):                    # all-or-nothing, r representative
            m |= 1 << i
    CM[w] = m
FULL = (1 << p) - 1

def coverable_by_5(target):
    """Can 5 coarse dilates cover the class set `target`?  Branch on lowest missing."""
    def rec(mask, depth):
        rem = target & ~mask
        if rem == 0:
            return True
        if depth == 5:
            return False
        lb = (rem & -rem).bit_length() - 1
        for w in coarse_w:
            if (CM[w] >> lb) & 1:
                if rec(mask | CM[w], depth + 1):
                    return True
        return False
    return rec(0, 0)

hist = {}
survivors = []
for v1, v2 in combinations(odd, 2):
    a, b = B[v1], B[v2]
    D = (a[0] | b[0]) & (a[1] | b[1]) & (a[2] | b[2]) & (a[3] | b[3])
    c = D.bit_count()
    hist[c] = hist.get(c, 0) + 1
    if c >= 12:
        survivors.append((v1, v2, D))

print("pairs of odd speeds:", len(odd) * (len(odd) - 1) // 2)
print("distribution of |D| = # classes the odd pair fully covers:")
for c in sorted(hist):
    print(f"   |D| = {c:>3}   {hist[c]:>8} pairs")
print("max |D| over all pairs:", max(hist))
print("threshold needed (U_min(5) = 163 - max union of 5 dilates):", 12)
print("pairs passing the |D| >= 12 filter:", len(survivors))

bad = None
for v1, v2, D in survivors:
    if coverable_by_5(FULL & ~D):
        bad = (v1, v2, D); break
print("bad cover with x = 5 :", "FOUND " + str(bad[:2]) if bad else "NONE (sector closed)")
