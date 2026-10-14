"""Grid plus deviation, and where the cascade's landing sits (exact Fractions, no floats).

Map: MECHANISM_MAP_v5 s.5, E299/E301.  Every set of 7 distinct positive integer disparities with gcd 1 and
largest <= N.  d_min = m.  Grid through d_min: y = m*q_y + r_y, 0 <= r_y < m; slot s_y = q_y mod 8; eps_y = r_y/m.
Cascade coordinate R = 8*m*t, reading rho_y = y/m.  Reading y blocks R iff R*rho_y lies in an open interval
(8z-1, 8z+1); the move goes to the largest next opening (8z+1)/rho_y among blockers; start R = 1.
Per arrangement: moves, the opener of the landing (rank, lap z), and the opener's grid slot and eps at the start.
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
        z = floor(x / 8 + F(1, 2))          # nearest multiple of 8, as x/8 rounded
        if abs(x - 8 * z) < 1:
            out.append((i, z, (8 * z + 1) / r))
    return out


def cascade(rho):
    R = F(1)
    moves = 0
    opener = (0, 0)                          # reading 1, lap 0: R = 1 is its opening (8*0+1)/1
    first_blk = None
    while True:
        b = blockers(R, rho)
        if first_blk is None:
            first_blk = [i for i, _, _ in b]
        if not b:
            return R, moves, opener, first_blk
        i, z, nxt = max(b, key=lambda t: t[2])
        assert nxt > R
        R, opener, moves = nxt, (i, z), moves + 1
        if moves > 400:
            return None, moves, opener, first_blk


tot = 0
fail = 0
mv = Counter()
cls = Counter()
lap = Counter()
nb0 = Counter()
rank = Counter()
exceptions = []
for S in combinations(range(1, N + 1), 7):
    if reduce(gcd, S) != 1:
        continue
    tot += 1
    m = S[0]
    rho = [F(y, m) for y in S]
    R, moves, (oi, oz), first = cascade(rho)
    if R is None:
        fail += 1
        continue
    mv[moves] += 1
    q = [y // m for y in S]
    eps = [F(y % m, m) for y in S]
    slot = [qq % 8 for qq in q]
    # grid blockers at the start: slot 0 always (rho in [8k, 8k+1)), slot 7 with eps > 0
    pred = sorted(i for i in range(7) if slot[i] == 0 or (slot[i] == 7 and eps[i] > 0))
    if pred != sorted(first):
        exceptions.append((S, pred, sorted(first)))
    if moves == 0:
        cls["no move"] += 1
    else:
        c = (slot[oi], "eps>0" if eps[oi] > 0 else "eps=0")
        cls[c] += 1
        lap[oz] += 1
        rank[oi + 1] += 1
        nb0[len(first)] += 1

print("N =", N, " sets (gcd 1, 7 disparities):", tot, " cascade did not fix within 400 moves:", fail)
print("moves:", sorted(mv.items()))
print("start blockers = grid prediction (slot 0, or slot 7 with eps>0): exceptions", len(exceptions), exceptions[:3])
print("opener of the landing, (slot at start, eps) for moved arrangements:")
for k, v in sorted(cls.items(), key=lambda t: -t[1]):
    print("   ", k, v)
print("opener rank (1 = d_min):", sorted(rank.items()))
print("opener lap z:", sorted(lap.items()))
print("number of start blockers (moved):", sorted(nb0.items()))
