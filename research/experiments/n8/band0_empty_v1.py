"""Random sampling finds no band-0-empty profile, but the manuscript records deep cases with
R in [10.26, 11.97] -- which ARE band-0-empty.  Search for them deliberately.

Hill-climb on rational readings to maximise the minimum clear point R.
"""
from fractions import Fraction as F
import random

def clear(S, x):
    for s in S:
        y = s*x
        if abs(y - 8*round(y/8)) < 1: return False
    return True

def Rval(S, hi=F(16), step=F(1,480)):
    """least clear x >= 1, on a fine grid; None if none below hi."""
    x = F(1)
    while x <= hi:
        if clear(S, x): return x
        x += step
    return None

rng = random.Random(20260919)
best = None
for restart in range(300):
    S = [F(1)] + sorted(F(rng.randint(2, 60), rng.randint(1, 8)) for _ in range(6))
    if len(set(S)) != 7 or min(S) != 1: continue
    cur = Rval(S)
    if cur is None: continue
    for _ in range(400):
        T = list(S); i = rng.randrange(1, 7)
        T[i] = F(max(1, T[i].numerator + rng.choice([-3,-2,-1,1,2,3])), T[i].denominator)
        T = sorted(set(T))
        if len(T) != 7 or min(T) != 1: continue
        v = Rval(T)
        if v is not None and v > cur: S, cur = T, v
    if best is None or cur > best[0]: best = (cur, list(S))
print(f"largest minimum-clear-point found: R = {best[0]} = {float(best[0]):.4f}")
print(f"  profile: {[str(s) for s in best[1]]}")
print(f"  band 0 empty? {best[0] > 7}")
print()
# direct check: can band 0 be empty at all?
found = None
for restart in range(4000):
    S = [F(1)] + sorted(F(rng.randint(2, 200), rng.randint(1, 12)) for _ in range(6))
    if len(set(S)) != 7 or min(S) != 1: continue
    x = F(1); ok = False
    while x <= 7:
        if clear(S, x): ok = True; break
        x += F(1,480)
    if not ok:
        found = S; break
print(f"band-0-empty profile found by direct search: {'YES ' + str([str(s) for s in found]) if found else 'no'}")
print(f"\n  NOTE: the manuscript records deep cases in band 1 (R = 10.26 .. 11.97), so band-0-empty")
print(f"  profiles exist. Absence here is a statement about this search, not about the objects.")
