"""The synchronised-block rule, and its N-free reduced problem R.

Block F = {N + e_i}, 0 = e_0 < ... < e_{f-1} = E; core C.  Over [t0, t0 + 1/N] the common phase N t
makes one full turn while each offset e_i t moves at most E/N.  So if C is clear on that stretch and
the points {e_i t0 mod 1} leave a cyclic gap >= 1/4 + 2E/N, some instant in it clears everything.
For large N this reduces to
    R(C, e):  some t in the INTERIOR of C's clear set with the points {e_i t} having a cyclic gap > 1/4.
Part 1: R tested exhaustively for the shapes the separation side lacks: f = 5 (core of 2, offsets
{0} + 4 from [1,B]) and f = 6 (core of 1, offsets {0} + 5 from [1,B]), C from [1,B].  Exact: between
consecutive breakpoints (order changes (e_i - e_j) t in Z, core zone endpoints) the cyclic order is
fixed and each gap is linear in t, so the max gap peaks at a breakpoint; C-clear is tested at
breakpoints and at midpoints (interior).  Integer speeds: period 1.
Part 2: the full rule on sets C u {N + e_i}, N = 10^6: the constructed instant checked exactly.
"""
import sys, time, random
from fractions import Fraction as Fr
from itertools import combinations
from math import floor, ceil
B = int(sys.argv[1]) if len(sys.argv) > 1 else 12
def nd(x): x = x % 1; return min(x, 1 - x)
def max_gap(pts):
    p = sorted(x % 1 for x in pts); g = [p[i + 1] - p[i] for i in range(len(p) - 1)] + [1 - p[-1] + p[0]]
    i = max(range(len(g)), key=lambda k: g[k]); return g[i], p[i]      # gap length and its start
def core_clear_open(C, t, eps): return all(nd(c * (t + s)) >= Fr(1, 8) for c in C for s in (-eps, 0, eps))
def R_holds(C, e):
    bps = {Fr(0), Fr(1)}
    for c in C:
        for m in range(c + 1):
            for s in (-1, 1):
                x = Fr(8 * m + s, 8 * c)
                if 0 <= x <= 1: bps.add(x)
    for i in range(len(e)):
        for j in range(i + 1, len(e)):
            dd = e[j] - e[i]
            for m in range(dd + 1): bps.add(Fr(m, dd))
    bps = sorted(bps)
    cand = bps + [(bps[k] + bps[k + 1]) / 2 for k in range(len(bps) - 1)]
    for t in cand:
        if t <= 0: continue
        if max_gap([ei * t for ei in e])[0] > Fr(1, 4) and core_clear_open(C, t, Fr(1, 10**9)):
            return t
    return None
t0 = time.time(); fails = []; n = 0
for f, c in ((5, 2), (6, 1)):
    for C in combinations(range(1, B + 1), c):
        for off in combinations(range(1, B + 1), f - 1):
            n += 1; e = (0,) + off
            if R_holds(C, e) is None: fails.append((C, e))
print(f"Part 1: R(C, e) for f=5 (core 2) and f=6 (core 1), speeds in [1,{B}]: {n} cases, fails {len(fails)} {fails[:5]}  ({time.time() - t0:.0f}s)")
# Part 2: the full rule, exact
rnd = random.Random(45); ok = tot = 0; N = 10**6
for _ in range(300):
    f = rnd.choice((5, 6)); c = 7 - f
    C = tuple(sorted(rnd.sample(range(1, 30), c))); e = (0,) + tuple(sorted(rnd.sample(range(1, 30), f - 1)))
    t_star = R_holds(C, e)
    if t_star is None: continue
    tot += 1; E = e[-1]
    gl, gs = max_gap([ei * t_star for ei in e])
    target = gs + gl / 2                         # middle of the free arc, for the offsets
    phi_now = (N * t_star) % 1
    t = t_star + ((-target - phi_now) % 1) / N   # N t = -target (mod 1): block readings = offsets - target
    S = C + tuple(N + ei for ei in e)
    ok += all(nd(d * t) >= Fr(1, 8) for d in S)
print(f"Part 2: full sets C u {{10^6 + e_i}}: the constructed instant is lonely (exact) in {ok}/{tot}")
