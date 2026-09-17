"""Is the determinator the same object in the framework's own coordinate -- scales, not times?

MANUSCRIPT_v9_1 section 6.1 defines the cascade in the TIME coordinate: the move sends `t` to the
largest next opening among the runners in the way, from the bound `1/(8m)`. Section 6.2 says that same
cascade is a recursion on the SCALE, fixed by the speeds:

    D_0 = d_min,   D_{j+1} = D_j * min{ s/(8N + 1) : |s - 8N| < 1, s = d/D_j },   instant = 1/(8*D_final)

stopping when no reading is within 1 of a multiple of 8.

Everything on 2026-09-17 was computed in the time coordinate. If the two coordinates disagree, the time
implementation is not the framework's determinator. This checks them against each other on shuffled
arrangements and on the readings of the depth-14 cap word.

Both are exact rational arithmetic. No search, no candidates: each arrangement determines its own chain.
"""
import os, sys, random
from fractions import Fraction as F

n = 8
INV_N = F(1, n)

# ---- time coordinate (section 6.1; LRC/Cascade/Iteration.lean) ----
def fract(x):          return x - (x.numerator // x.denominator)
def circDist(x):       return min(fract(x), 1 - fract(x))
def inWay(d, t):       return circDist(d * t) < INV_N
def ceil_(x):          return -((-x.numerator) // x.denominator)
def nextOpening(d, t): return (F(ceil_(d * t - INV_N)) + INV_N) / d
def Lonely(ds, s):     return all(INV_N <= circDist(d * s) for d in ds)
def move(ds, t):
    acc = t
    for d in ds:
        if inWay(d, t):
            o = nextOpening(d, t)
            if o > acc: acc = o
    return acc
def cascade_time(ds, maxsteps=2000):
    t = F(1, n * min(ds))                      # the bound 1/(8m)
    for k in range(maxsteps):
        t2 = move(ds, t)
        if t2 == t: return t, k
        t = t2
    return None, maxsteps

# ---- scale coordinate (section 6.2) ----
def cascade_scale(ds, maxsteps=2000):
    D = min(ds)                                 # D_0 = d_min
    for k in range(maxsteps):
        best = None
        for d in ds:
            s = F(d, 1) / D if not isinstance(d, F) else d / D
            N = round(s / 8)                    # |s - 8N| < 1 fixes N
            if abs(s - 8 * N) < 1:
                cand = s / (8 * N + 1)          # D_{j+1} = D * s/(8N+1)
                if best is None or cand < best: best = cand
        if best is None: return F(1, 8 * D), k  # no reading within 1 of a multiple of 8
        D = D * best
    return None, maxsteps

def check(ds, label):
    t_t, k_t = cascade_time(ds)
    t_s, k_s = cascade_scale(ds)
    ok = (t_t == t_s)
    return ok, t_t, t_s, k_t, k_s

print("order 8: the determinator in two coordinates -- time (section 6.1) vs scale (section 6.2)\n")

# the depth-14 cap word's readings, from ladder_cap_word_replay_v1
cap_cases = [
    ("cap word, max-margin", [F(1), F(8), F(124160,19863), F(32744,6621), F(9664,2207), F(24128,6621), F(299584,103729)]),
    ("cap word, tau>=1/10^6", [F(1), F(875001,125000), F(765626,140625), F(84291747,19375000), F(1859377,484375), F(179119943,55703125), F(1859377,734375)]),
]
for label, ds in cap_cases:
    ok, t_t, t_s, k_t, k_s = check(ds, label)
    print(f"  {label:24}  time {str(t_t):>22}  scale {str(t_s):>22}  agree {ok}"
          f"   (steps {k_t}/{k_s})")

print()
random.seed(20260917)
agree = 0; disagree = []; tested = 0
for _ in range(4000):
    while True:
        dsi = random.sample(range(1, 201), 7); m = min(dsi)
        if max(dsi) <= 8 * m: break
    ds = sorted(F(d) for d in dsi)
    ok, t_t, t_s, k_t, k_s = check(ds)  if False else check(ds, '')
    tested += 1
    if ok: agree += 1
    elif len(disagree) < 3: disagree.append((ds, t_t, t_s))
print(f"  shuffled arrangements (ratio <= 8, entries <= 200): {agree}/{tested} agree")
for ds, a, b in disagree:
    print(f"    DISAGREE {[str(x) for x in ds]}  time {a}  scale {b}")

random.seed(99)
agree2 = 0; tested2 = 0
for _ in range(2000):
    while True:
        dsi = random.sample(range(1, 401), 7); m = min(dsi)
        if max(dsi) <= 40 * m: break
    ds = sorted(F(d) for d in dsi)
    ok, *_ = check(ds, '')
    tested2 += 1; agree2 += ok
print(f"  shuffled arrangements (ratio <= 40, entries <= 400): {agree2}/{tested2} agree")
