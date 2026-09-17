"""Directed search for large R at order 8 -- the calibration my random sweep lacked.

`first_window_nativeness_v2.py` sampled shuffled integer difference sets and found 0 of 28,000 with the
first lonely instant beyond u = (n-1)/n. MANUSCRIPT_v9_1 section 6.7 records `R ~ 11.96` at `S ~ 7.44`,
which is u ~ 1.495 -- far beyond it. A random sweep returning a clean null where a directed search
throws off extremes is the documented suppression signature, so the null is tested here rather than
reported.

R = n * u with u the first lonely instant in laps (section 6.2 identity, verified in
`scale_recursion_check_v1.py`). Random restarts plus hill climbing on the difference set, exact
rational arithmetic, the determinator of section 6.1.
"""
import os, sys, random
from fractions import Fraction as F

n = 8; INV_N = F(1, n); NDIFF = n - 1

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

def R_of(dsi, maxsteps=3000):
    """R = n * u, u the first lonely instant in laps. dsi: integer differences."""
    ds = [F(d) for d in dsi]; m = min(ds)
    t = F(1, 1) / (n * m)                       # the bound 1/(n*d_min)
    for k in range(maxsteps):
        t2 = move(ds, t)
        if t2 == t:
            u = m * t                            # laps: u = d_min * t
            return n * u, k, t
        t = t2
    return None, maxsteps, None

VMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 400
RESTARTS = int(sys.argv[2]) if len(sys.argv) > 2 else 300
random.seed(20260917)
CAP = n - 1

print(f"order {n}: directed search for large R = n*u, u = first lonely instant in laps")
print(f"cap (first window) R < {CAP};  manuscript section 6.7 records R ~ 11.96 at S ~ 7.44\n")

best = (F(0), None)
found_over = 0; tried = 0
for r in range(RESTARTS):
    cur = sorted(random.sample(range(1, VMAX + 1), NDIFF))
    Rc, _, _ = R_of(cur)
    if Rc is None: continue
    improved = True
    while improved:
        improved = False
        for i in range(NDIFF):
            for delta in (-3, -2, -1, 1, 2, 3):
                cand = list(cur); cand[i] += delta
                if cand[i] < 1 or cand[i] > VMAX or len(set(cand)) < NDIFF: continue
                cand = sorted(cand); tried += 1
                Rn, _, _ = R_of(cand)
                if Rn is not None and Rn > Rc:
                    cur, Rc = cand, Rn; improved = True
    if Rc > CAP: found_over += 1
    if Rc > best[0]: best = (Rc, list(cur))

R, ds = best
m = min(ds); S = F(max(ds), m)
print(f"  restarts {RESTARTS}, candidates evaluated {tried}")
print(f"  hill-climbs ending above the cap: {found_over}/{RESTARTS}")
print(f"\n  largest R found: {R} = {float(R):.4f}    cap {CAP}    {'ABOVE THE CAP' if R > CAP else ''}")
print(f"    differences {ds}   d_min {m}   ratio S = {S} = {float(S):.4f}")
Rv, steps, t = R_of(ds)
u = F(m) * t
print(f"    first lonely instant t = {t},  u = d_min*t = {u} = {float(u):.4f} laps, {steps} moves")
print(f"    lonely there: {Lonely([F(d) for d in ds], t)}")
print(f"\n  u > (n-1)/n = {float(F(n-1,n)):.4f} (beyond the first window): {u > F(n-1,n)}")
