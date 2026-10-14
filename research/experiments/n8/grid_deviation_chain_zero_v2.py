"""Recount slot descent with 0 read as 0, against 0 read as 8, and against rank fall.  Exact Fractions.

Population as grid_deviation_chain_rank_v1.py (7-subsets of [1,N], gcd 1, landing opened by a clear-at-start reading).
D8 = start slots strictly decreasing, slot 0 read as 8.   D0 = strictly decreasing, slot 0 read as 0.
F  = reading (rank) falls at every step.   Counts only.
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
        chain.append(i)
        R = nxt


c = Counter()
n = 0
first_slot0 = Counter()
split = Counter()
for S in combinations(range(1, N + 1), 7):
    if reduce(gcd, S) != 1:
        continue
    m = S[0]
    rho = [F(y, m) for y in S]
    slot0 = [(y // m) % 8 for y in S]
    epos = [y % m != 0 for y in S]
    start_blk = [slot0[i] == 0 or (slot0[i] == 7 and epos[i]) for i in range(7)]
    chain = run(rho)
    if not chain or start_blk[chain[-1]]:
        continue
    n += 1
    s8 = [8 if slot0[i] == 0 else slot0[i] for i in chain]
    s0 = [slot0[i] for i in chain]
    D8 = all(s8[k] > s8[k + 1] for k in range(len(chain) - 1))
    D0 = all(s0[k] > s0[k + 1] for k in range(len(chain) - 1))
    Fall = all(chain[k + 1] < chain[k] for k in range(len(chain) - 1))
    c[("D8", D8)] += 1
    c[("D0", D0)] += 1
    c[("F", Fall)] += 1
    c[("D8,D0", D8, D0)] += 1
    c[("D0,F", D0, Fall)] += 1
    c[("D8,F", D8, Fall)] += 1
    first_slot0[slot0[chain[0]]] += 1
    split[(slot0[chain[0]], 'D8' if D8 else 'notD8', 'D0' if D0 else 'notD0')] += 1

print("N =", N, " chains:", n)
for k in [("D8", True), ("D8", False), ("D0", True), ("D0", False), ("F", True), ("F", False)]:
    print("  ", k, c[k])
print("D8 against D0:")
for a in (True, False):
    for b in (True, False):
        print("   D8=%s D0=%s : %d" % (a, b, c[("D8,D0", a, b)]))
print("D0 against F (agree = same truth value):")
for a in (True, False):
    for b in (True, False):
        print("   D0=%s F=%s : %d" % (a, b, c[("D0,F", a, b)]))
print("first setter's start slot (0 shown as 0):", sorted(first_slot0.items()))

# v2: split of D8 chains by the first setter's start slot (counted, not inferred)
print('D8/D0 split by first setter slot (slot, D8, D0):')
for k,v in sorted(split.items()):
    print('  ',k,v)
