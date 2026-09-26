"""The one hard case (author): two runners in one slot.  Read as a grid (reduced by g, residues mod 8), at a grid
instant p/(8g) a runner is clear unless another runner shares ITS residue (Thm 4.11).  So a doubled slot delays exactly
the two runners in it; the other six are lonely at 1/(8g).
Build: AP reduced speeds 0..7 (all speeds +100, so all positive); move the runner with residue r to s + 8m.  Slot s is
doubled (pair 8m apart), slot r is empty.  Every runner, exact cascade.  Recorded: delayed or not (event later than
1/(8g)); the event in grid eighths R = 8*g*t*; the pair's relative laps at t* (8m*t*); flank rank and lap; the distance
from the pair to its nearest third runner."""
from fractions import Fraction as F
from math import floor, gcd
from functools import reduce
from collections import defaultdict

def nd(x): x = x % 1; return min(x, 1 - x)
def event(V, k):
    ds = [abs(v - V[k]) for j, v in enumerate(V) if j != k]
    t = F(1, 8 * min(ds)); moves = 0
    while True:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return t, moves
        t = max((F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way); moves += 1

rows = []
for s in range(8):
    for r in range(8):
        if r == s: continue
        for m in range(1, 9):
            U = [x for x in range(8) if x != r] + [s + 8 * m]
            V = sorted(100 + u for u in U)
            g = reduce(gcd, [v - V[0] for v in V[1:]])
            pair = [100 + s, 100 + s + 8 * m]
            third = min(abs(v - p) for v in V if v not in pair for p in pair)
            for k in range(8):
                t, mv = event(V, k)
                delayed = t > F(1, 8 * g)
                rows.append(dict(s=s, r=r, m=m, g=g, V=V, k=k, in_pair=V[k] in pair, t=t, R=8 * g * t, moves=mv,
                                 delayed=delayed, third=third, pairlaps=8 * m * t))
n_pair = [x for x in rows if x['in_pair']]; n_rest = [x for x in rows if not x['in_pair']]
print(f"{len(rows) // 8} arrangements, {len(rows)} runners (g = 1 in all: {all(x['g'] == 1 for x in rows)})")
print(f"runners NOT in the doubled slot: delayed {sum(x['delayed'] for x in n_rest)} of {len(n_rest)}")
print(f"runners IN the doubled slot:     delayed {sum(x['delayed'] for x in n_pair)} of {len(n_pair)}")
print("\nthe pair's event R = 8t* (grid eighths), by separation m (rows) and empty slot r relative to s (cols, (r-s) mod 8):")
tab = defaultdict(set)
for x in n_pair: tab[(x['m'], (x['r'] - x['s']) % 8)].add(x['R'])
print("   m  " + "".join(f"{c:>22}" for c in range(1, 8)))
for m in range(1, 9):
    cells = []
    for c in range(1, 8):
        vals = sorted(tab[(m, c)]); cells.append(f"{float(min(vals)):.3f}..{float(max(vals)):.3f}")
    print(f"   {m}  " + "".join(f"{z:>22}" for z in cells))
print("\nthe pair's relative laps at their event (8m*t*), min..max by m:")
for m in range(1, 9):
    v = [x['pairlaps'] for x in n_pair if x['m'] == m]
    print(f"   m={m}: {float(min(v)):.3f} .. {float(max(v)):.3f};  moves max {max(x['moves'] for x in n_pair if x['m']==m)}")
