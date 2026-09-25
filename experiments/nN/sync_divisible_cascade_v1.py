"""Divisible cores (a core runner divisible by 7, which the seventh-grid rule does not reach): read the
cascade's isolation event on the FULL set, as the owner asks, instead of searching grids.

Sets S = C u {N + e_i}: f = 6 with core {c}, 7 | c; f = 5 with core {c1, c2}, 7 | one of them;
offsets 0 = e_0 < ... random in [1, 60]; N = 10^5.  Exact cascade from the bound 1/(8 d_min).
Reported for the isolation event t*: which runner pins it (reads exactly 1/8 or 7/8), whether it is a
core or block runner; the core readings; the nearest fraction a/q to t* with q <= 24; the largest
gap of the offsets {e_i t*}; whether t* lies before 3/(4E) (the easy case).
"""
import random
from fractions import Fraction as F
from math import floor
from collections import Counter
def nd(x): x = x % 1; return min(x, 1 - x)
def cascade(S):
    t = F(1, 8 * min(S))
    while True:
        way = [d for d in S if nd(d * t) < F(1, 8)]
        if not way: return t
        t = max((F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way)
def max_gap(pts):
    p = sorted(set(x % 1 for x in pts)); g = [p[i + 1] - p[i] for i in range(len(p) - 1)] + [1 - p[-1] + p[0]]
    return max(g)
def nearest_small(t, Q=24):
    return min(((abs(t - F(round(t * q), q)), q, round(t * q)) for q in range(1, Q + 1)))
rnd = random.Random(48); N = 10**5
pin = Counter(); easy = Counter(); qs = Counter(); rows = []
for trial in range(400):
    f = rnd.choice((5, 6))
    if f == 6: C = [7 * rnd.randrange(1, 9)]
    else: C = sorted([7 * rnd.randrange(1, 9), rnd.randrange(1, 60)])
    e = [0] + sorted(rnd.sample(range(1, 61), f - 1)); E = e[-1]
    S = sorted(set(C + [N + x for x in e]))
    if len(S) < 7: continue
    t = cascade(S)
    pinner = [d for d in S if (d * t) % 1 in (F(1, 8), F(7, 8))]
    kind = 'core' if all(d in C for d in pinner) else ('block' if all(d not in C for d in pinner) else 'both')
    pin[kind] += 1
    easy['before 3/(4E)' if t < F(3, 4 * E) else 'later'] += 1
    dist, q, a = nearest_small(t); qs[q if dist * N < 2 else 'none within 2/N'] += 1
    if len(rows) < 6: rows.append((C, e, t, float(t), pinner, [str(F(round(float((c * t) % 1) * 1000), 1000)) for c in C], float(max_gap([x * t for x in e]))))
print(f"400 divisible-core sets, N = 10^5: pinned by {dict(pin)};  isolation {dict(easy)}")
print(f"   nearest a/q (q <= 24) within 2/N of t*: {sorted(qs.items(), key=lambda x: str(x[0]))}")
for C, e, t, tf, pinner, cr, g in rows:
    print(f"   core {C}, offsets {e}: t* = {tf:.6f}; pinned by {[p if p in C else f'N+{p - N}' for p in pinner]}; core readings {cr}; offsets' largest gap {g:.3f}")

# the LATER events (after 3/(4E)): what pins them, where the core is, how the offsets sit
print("later events (t* >= 3/(4E)):")
rnd = random.Random(48); shown = 0; kinds = Counter(); core_lap = Counter(); gaps = []
for trial in range(400):
    f = rnd.choice((5, 6))
    if f == 6: C = [7 * rnd.randrange(1, 9)]
    else: C = sorted([7 * rnd.randrange(1, 9), rnd.randrange(1, 60)])
    e = [0] + sorted(rnd.sample(range(1, 61), f - 1)); E = e[-1]
    S = sorted(set(C + [N + x for x in e]))
    if len(S) < 7: continue
    t = cascade(S)
    if t < F(3, 4 * E): continue
    pinner = [d for d in S if (d * t) % 1 in (F(1, 8), F(7, 8))]
    kinds['core' if all(d in C for d in pinner) else 'block'] += 1
    cmin = min(C); core_lap[floor(cmin * t)] += 1
    g = max_gap([x * t for x in e]); gaps.append(g)
    if shown < 6:
        shown += 1
        print(f"   core {C}, offsets {e} (E/c_min = {E / cmin:.1f}): t* = {float(t):.5f} = {float(t * cmin):.3f} laps of c_min; "
              f"pinned by {[p if p in C else f'N+{p - N}' for p in pinner]}; offsets' largest gap {float(g):.3f}")
print(f"   pinned by {dict(kinds)};  laps of c_min completed at t*: {sorted(core_lap.items())};  offsets' largest gap: min {float(min(gaps)):.3f}")
