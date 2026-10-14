"""Item 4 of grid_deviation_landing_v1: the chain from the first displacement to an opener that was clear at the start.

Same objects as grid_deviation_landing_v1.py (exact Fractions; all 7-subsets of [1,N], gcd 1; d_min = m;
slot = floor(y/m) mod 8, eps>0 iff m does not divide y).  For every set whose landing opener is NOT a start blocker
(slot 0, or slot 7 with eps>0), record the chain: each move's setter as (slot, eps>0, lap z), and the opener.
Counts only; no rule is asserted.
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
            return R, chain
        i, z, nxt = max(b, key=lambda t: t[2])
        chain.append((i, z, len(b)))
        R = nxt


sig = Counter()
nmoved = ncl = 0
len_by = Counter()
first_cat = Counter()
last_setter_is_blocker_cat = Counter()
extra_blockers_second = Counter()
for S in combinations(range(1, N + 1), 7):
    if reduce(gcd, S) != 1:
        continue
    m = S[0]
    rho = [F(y, m) for y in S]
    slot = [(y // m) % 8 for y in S]
    epos = [y % m != 0 for y in S]
    isstart = [slot[i] == 0 or (slot[i] == 7 and epos[i]) for i in range(7)]
    R, chain = run(rho)
    if not chain:
        continue
    nmoved += 1
    oi = chain[-1][0]
    if isstart[oi]:
        continue
    ncl += 1
    s = tuple((slot[i], "+" if epos[i] else "0", z) for i, z, _ in chain)
    len_by[len(chain)] += 1
    # the signature without laps: slot and eps of each setter
    sig[tuple((a, b) for a, b, _ in s)] += 1
    first_cat[(s[0][0], s[0][1])] += 1
    # was the opener a setter earlier in the chain?
    earlier = any(i == oi for i, _, _ in chain[:-1])
    last_setter_is_blocker_cat[("opener also set an earlier move" if earlier else "opener sets only the last move")] += 1

print("N =", N, " moved:", nmoved, " opener clear at start:", ncl)
print("chain length (moves) for these:", sorted(len_by.items()))
print("first setter (start slot, eps):", sorted(first_cat.items(), key=lambda t: -t[1]))
print(dict(last_setter_is_blocker_cat))
print("distinct slot/eps signatures:", len(sig))
for k, v in sig.most_common(25):
    print("  ", v, " ".join(f"{a}{b}" for a, b in k))

# v2: is the setter-slot sequence strictly decreasing with slot 0 read as 8?  (counted over all chains above)
dec = nondec = 0
viol = []
for k, v in sig.items():
    s = [8 if a == 0 else a for a, _ in k]
    if all(s[i] > s[i + 1] for i in range(len(s) - 1)):
        dec += v
    else:
        nondec += v
        viol.append((v, k))
print("setter slots strictly decreasing (0 as 8):", dec, " not:", nondec)
for v, k in sorted(viol, reverse=True)[:10]:
    print("  not decreasing:", v, " ".join(f"{a}{b}" for a, b in k))
