#!/usr/bin/env python3
"""Decide the x=4 sector of Lemma 7 at k=7, p=163.

x = #{v in T : 8 | v}.  x=4 leaves m=3 non-coarse speeds, of which at least two
must be odd (the gcd condition needs two odd speeds and the coarse ones are even).
Four dilates of the 41-arc leave at least U_min(4) = 163 - 129 = 34 classes
uncovered, and those must be fully covered by the 3 non-coarse speeds:

    D(v1,v2,v3) = { r : S_v1(r) u S_v2(r) u S_v3(r) = {0,1,2,3} }
    necessary:  |D| >= 34;  exact:  complement(D) coverable by 4 dilates.
"""
import sys
from itertools import combinations

N, H, p = 1304, 652, 163
NEED = 34

def covers(j, v):
    r = (j * v) % N
    return r < p or r > N - p

def v2(v):
    e = 0
    while v % 2 == 0:
        v //= 2; e += 1
    return e

speeds = [v for v in range(1, H + 1) if v % p != 0]
odd = [v for v in speeds if v % 2 == 1]
noncoarse = [v for v in speeds if v2(v) < 3]
coarse_w = list(range(1, H // 8 + 1))

B = {}
for v in noncoarse:
    bs = [0, 0, 0, 0]
    for i, r in enumerate(range(1, p + 1)):
        for t in range(4):
            if covers(r + p * t, v):
                bs[t] |= 1 << i
    B[v] = bs

CM = {}
for w in coarse_w:
    m = 0
    for i, r in enumerate(range(1, p + 1)):
        if covers(r, 8 * w):
            m |= 1 << i
    CM[w] = m
FULL = (1 << p) - 1

def coverable(target, budget):
    def rec(mask, depth):
        rem = target & ~mask
        if rem == 0:
            return True
        if depth == budget:
            return False
        lb = (rem & -rem).bit_length() - 1
        for w in coarse_w:
            if (CM[w] >> lb) & 1 and rec(mask | CM[w], depth + 1):
                return True
        return False
    return rec(0, 0)

best = -1
survivors = []
npairs = 0
for v1, v2 in combinations(odd, 2):
    a, b = B[v1], B[v2]
    A = [a[t] | b[t] for t in range(4)]
    # upper bound: classes where the pair already has >=2 of the 4 targets
    #   (a third speed contributes at most 2), plus the already-full ones
    full2 = A[0] & A[1] & A[2] & A[3]
    ub = 0
    for s, t in combinations(range(4), 2):
        ub |= A[s] & A[t]
    if (ub | full2).bit_count() < NEED:
        npairs += 1
        continue
    for v3 in noncoarse:
        if v3 == v1 or v3 == v2:
            continue
        c = B[v3]
        D = (A[0] | c[0]) & (A[1] | c[1]) & (A[2] | c[2]) & (A[3] | c[3])
        n = D.bit_count()
        if n > best:
            best = n
        if n >= NEED:
            survivors.append((v1, v2, v3, D))
print("odd pairs discarded by the >=2-of-4 upper bound:", npairs, "of", len(odd)*(len(odd)-1)//2)
print("max |D| over triples (2+ odd):", best, " needed:", NEED)
print("triples passing the count filter:", len(survivors))
sys.stdout.flush()
bad = None
for v1, v2, v3, D in survivors:
    if coverable(FULL & ~D, 4):
        bad = (v1, v2, v3); break
print("bad cover with x = 4 :", "FOUND " + str(bad) if bad else "NONE (sector closed)")
