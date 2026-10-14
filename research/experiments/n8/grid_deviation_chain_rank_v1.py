"""Rank versus start slot along the chain (exact Fractions; same population as grid_deviation_chain_v2.py).

For every 7-subset of [1,N] with gcd 1 whose landing is opened by a reading that is NOT a start blocker, record the
setters in order as (rank by reading, lap, start slot with 0 read as 8).  Transitions follow E142:
sweep (slower, same lap), bridge down (slower, earlier lap), bridge up (faster, later lap).
Crosstab: D = start slots strictly decreasing (0 as 8)  against  B = chain contains a bridge up,
and against  F = rank strictly falls at every step.  Counts only; nothing asserted.
"""
import sys
from fractions import Fraction as F
from itertools import combinations
from math import gcd, floor
from collections import Counter
from functools import reduce

N = int(sys.argv[1]) if len(sys.argv) > 1 else 22


def blockers(R, rho):
    out = []
    for i, r in enumerate(rho):
        x = R * r
        z = floor(x / 8 + F(1, 2))
        if abs(x - 8 * z) < 1:
            out.append((i, z, (8 * z + 1) / r))
    return out


def run(rho):
    R, chain = F(1), []
    while True:
        b = blockers(R, rho)
        if not b:
            return chain
        i, z, nxt = max(b, key=lambda t: t[2])
        chain.append((i, z))
        R = nxt


cross_B = Counter()
cross_F = Counter()
kinds = Counter()
ex_notD_noB = []
ex_D_B = []
n = 0
for S in combinations(range(1, N + 1), 7):
    if reduce(gcd, S) != 1:
        continue
    m = S[0]
    rho = [F(y, m) for y in S]
    slot = [(y // m) % 8 for y in S]
    epos = [y % m != 0 for y in S]
    start_blk = [slot[i] == 0 or (slot[i] == 7 and epos[i]) for i in range(7)]
    chain = run(rho)
    if not chain or start_blk[chain[-1][0]]:
        continue
    n += 1
    s8 = [8 if slot[i] == 0 else slot[i] for i, _ in chain]
    D = all(s8[k] > s8[k + 1] for k in range(len(s8) - 1))
    trans = []
    for k in range(len(chain) - 1):
        (a, ja), (b, jb) = chain[k], chain[k + 1]
        if b > a:
            t = "up"            # faster setter (higher reading); lap must be later by the link rule
        elif jb == ja:
            t = "sweep"
        else:
            t = "down"
        trans.append(t)
        kinds[t] += 1
    B = "up" in trans
    Fall = all(chain[k + 1][0] < chain[k][0] for k in range(len(chain) - 1))
    cross_B[(D, B)] += 1
    cross_F[(D, Fall)] += 1
    if (not D) and (not B) and len(ex_notD_noB) < 5:
        ex_notD_noB.append((S, [(i + 1, z, s8[k]) for k, (i, z) in enumerate(chain)]))
    if D and B and len(ex_D_B) < 5:
        ex_D_B.append((S, [(i + 1, z, s8[k]) for k, (i, z) in enumerate(chain)]))

print("N =", N, " chains with a clear-at-start opener:", n)
print("transitions (E142 types, by reading and lap):", dict(kinds))
print("D = slots strictly decreasing (0 as 8); B = chain has a bridge up")
for k in [(True, False), (True, True), (False, False), (False, True)]:
    print("   D=%s B=%s : %d" % (k[0], k[1], cross_B[k]))
print("F = reading (rank) strictly falls at every step")
for k in [(True, False), (True, True), (False, False), (False, True)]:
    print("   D=%s F=%s : %d" % (k[0], k[1], cross_F[k]))
print("examples not-D and no bridge up (S; chain as (rank, lap, slot)):")
for e in ex_notD_noB:
    print("  ", e)
print("examples D and bridge up:")
for e in ex_D_B:
    print("  ", e)
