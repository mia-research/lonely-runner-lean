"""Per-runner isolation at the AP is fixed by the two circle neighbours (owner, 2026-09-25).

AP speeds v_i = i, i = 1..8.  At the global event t = a/8 (a odd) the runners stand at the octagon's
vertices; subject k's circle neighbours are i = k +- a (mod 8) (a is its own inverse mod 8).  Deform
the speeds v_i = i*(1 + r_i), |r_i| <= rho.  Claim: with the other five still in their sections, k is
lonely at an OPENING OF ONE OF ITS TWO NEIGHBOURS near a/8 or near (8-a)/8 -- one of the mirror pair
{a, 8-a} always survives.  Test: for every subject k, each pair {1,7} and {3,5}, candidates are the
neighbour openings t = (N + 1/8)/|dv| nearest a/8 and (8-a)/8; lonely checked exactly (fractions).
"""
from fractions import Fraction as F
import random, math
def nd(x): x = x % 1; return min(x, 1 - x)
def cands(v, k, a):
    """openings (and closings) of the two neighbours of k at class a, nearest the nominal a/8"""
    out = []
    for i in ((k - 1 + a) % 8 + 1, (k - 1 - a) % 8 + 1):
        d = abs(v[i - 1] - v[k - 1])
        for base in (F(a, 8), F(8 - a, 8)):
            x = d * base                      # the neighbour's reading near the nominal instant
            for M in (math.floor(x) - 1, math.floor(x), math.floor(x) + 1):
                for s in (F(1, 8), F(7, 8)):
                    t = (M + s) / d
                    if t > 0: out.append(t)
    return out
def lonely(v, k, t): return all(nd((v[i] - v[k - 1]) * t) >= F(1, 8) for i in range(8) if i != k - 1)
rnd = random.Random(40)
for rho in (F(1, 20), F(1, 50), F(1, 100), F(1, 200)):
    ok = {1: 0, 3: 0}; tot = 0; fails = []
    for _ in range(1500):
        r = [F(rnd.randrange(-10**5, 10**5 + 1), 10**5) * rho for _ in range(8)]
        v = [(i + 1) * (1 + r[i]) for i in range(8)]
        for k in range(1, 9):
            tot += 1
            for a in (1, 3):
                if any(lonely(v, k, t) for t in cands(v, k, a)): ok[a] += 1
                elif len(fails) < 2: fails.append((k, a))
    print(f"|r| <= {rho}: subject-trials {tot};  pair {{1,7}} survives at a neighbour opening {ok[1]}/{tot};  pair {{3,5}} {ok[3]}/{tot};  e.g. failures {fails}")
