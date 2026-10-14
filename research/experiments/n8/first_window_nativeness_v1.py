"""Is the certificate's cap `R < n-1` a framework object, or the first window in lap coordinates?

OBJECT_REGISTER_v1 section 0 gives the framework's laps: `u = d_min * t`, readings `s_j = d_j/d_min`.
ORDER5_GROWTH_v2 section 2 gives `R = n * m * t` with `m = d_min`. So

    R = n * u    exactly,    and    R < n - 1   <=>   u < (n-1)/n .

The cascade opens at `t = 1/n`, i.e. `u = 1/n`. So the cap says exactly: `u` stays inside
`[1/n, (n-1)/n]` -- register item 15, **the first window**, classified MISPLACED, with the owner's
ruling recorded there: *"I never thought the first window/cycle was a requirement and think it keeps
getting introduced from context loss and revert to training data."*

If that identification is right, a cap violation is not a mathematical obstruction: it says the first
lonely instant lies in a later lap, which the framework permits. This script tests exactly that, using
only framework objects and the native cascade (`LRC/Cascade/Iteration.lean`, transcribed), with NO cap
and NO window restriction:

  * where does the first lonely instant actually fall, in laps `u`;
  * how often is it beyond `(n-1)/n`, so that the certificate would report NOT PROVED;
  * does the cascade still reach one.

Diverse sampling (shuffled integer difference sets, not lexicographic) per the standing rule.
"""
import os, sys, random
from fractions import Fraction as F

n = int(os.environ.get('ORDER', 8))
INV_N = F(1, n)
NDIFF = n - 1                       # differences from the subject: n-1 of them
CAP_U = F(n - 1, n)                 # the cap, in laps

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

def run(ds, maxsteps=4000):
    """Iterate to a fixed point. No cap, no window: every lap, as Iteration.lean's docstring says."""
    t = INV_N
    for k in range(maxsteps):
        t2 = move(ds, t)
        if t2 == t:
            return t, k, Lonely(ds, t)
    return t, maxsteps, None

S = int(sys.argv[1]) if len(sys.argv) > 1 else 8
NSAMP = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
DMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 60
random.seed(20260917)

print(f"order {n}: {NDIFF} differences, threshold 1/{n}, ratio bound S = {S}")
print(f"cap in laps: u < {CAP_U} = {float(CAP_U):.4f}   (equivalently R < {n-1})")
print(f"{NSAMP} shuffled integer difference sets, entries <= {DMAX}\n")

beyond = 0; inside = 0; nonterm = 0; worst = F(0); worst_ds = None
steps_hist = []; us = []
for _ in range(NSAMP):
    while True:
        ds = random.sample(range(1, DMAX + 1), NDIFF)
        m = min(ds)
        if max(ds) <= S * m: break
    readings = sorted(F(d, m) for d in ds)          # d_min normalised to 1
    t, k, lonely = run(readings)
    if lonely is None:
        nonterm += 1; continue
    u = t                                            # d_min = 1, so u = t
    us.append(u); steps_hist.append(k)
    if u > CAP_U:
        beyond += 1
        if u > worst: worst, worst_ds = u, readings
    else:
        inside += 1

tot = inside + beyond
print(f"  reached a lonely instant : {tot}/{NSAMP}   (no fixed point within the step budget: {nonterm})")
print(f"  first lonely instant INSIDE the first window (u <= {float(CAP_U):.4f}) : {inside}  ({100*inside/tot:.1f}%)")
print(f"  first lonely instant BEYOND it                                  : {beyond}  ({100*beyond/tot:.1f}%)")
if beyond:
    print(f"\n  largest u seen : {worst} = {float(worst):.4f}  (R = {n}*u = {float(n*worst):.4f}, cap {n-1})")
    print(f"     readings     : {[str(r) for r in worst_ds]}")
print(f"\n  cascade steps: min {min(steps_hist)}, median {sorted(steps_hist)[len(steps_hist)//2]}, max {max(steps_hist)}")
print(f"  laps u: min {float(min(us)):.4f}, max {float(max(us)):.4f}")
print()
if beyond:
    print(f"  => the first lonely instant lies beyond the first window in {100*beyond/tot:.1f}% of sampled")
    print(f"     arrangements, and the cascade reaches it. The cap is not a wall in the framework's")
    print(f"     objects; it is the boundary of the first window (register item 15).")
else:
    print(f"  => no sampled arrangement put the first lonely instant beyond the window at this ratio bound.")
