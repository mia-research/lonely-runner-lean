# THE load-bearing step. ExistenceAt8 <-> ExistenceAt8_cascade holds only if `move`
# never steps OVER a lonely instant.  If it could overshoot, the cascade form would be
# STRICTLY STRONGER than existence and we would be aiming at the wrong target.
#
#   move n ds t = max over blocking d of nextOpening(d,t)   (t if none block)
#
# Reasoning: if d blocks at t, then d keeps blocking throughout [t, nextOpening(d,t)),
# so no instant there is lonely.  Taking the MAX over blockers is therefore the largest
# provably-safe jump: the furthest blocker blocks the whole interval.  Test it.
import random
from fractions import Fraction as F
n = 8
def circ(x):
    f = x - (x.numerator // x.denominator); return min(f, 1-f)
def inway(d, t):  return circ(d*t) < F(1,n)
def nextop(d, t):
    from math import ceil
    q = d*t - F(1,n)
    c = -((-q.numerator)//q.denominator)      # exact ceil of a Fraction
    return (F(c) + F(1,n))/d
def move(ds, t):
    best = t
    for d in ds:
        if inway(d,t):
            o = nextop(d,t)
            if o > best: best = o
    return best

rng = random.Random(77)
overshoots = 0; steps = 0; sets = 0; arrived = 0
for _ in range(1500):
    ds = [F(x) for x in sorted(rng.sample(range(1,50), 7))]
    m = min(ds); t = F(1, n*m); sets += 1
    for _ in range(300):
        nt = move(ds, t)
        if nt == t: arrived += 1; break
        steps += 1
        # scan the OPEN interval (t, nt) for a lonely instant the move skipped
        for j in range(1, 40):
            u = t + (nt - t)*F(j,40)
            if all(circ(d*u) >= F(1,n) for d in ds):
                overshoots += 1
                print("  OVERSHOT:", [str(d) for d in ds], "t=",t, "->", nt, "lonely at", u)
                break
        t = nt
print(f"difference sets {sets}, cascades that arrived {arrived}, move steps examined {steps}")
print(f"steps that skipped a lonely instant : {overshoots}")
# control: a DELIBERATELY too-big jump must be caught by the same scan
bad = 0
rng3 = random.Random(5)
for _ in range(1500):
    ds = [F(x) for x in sorted(rng3.sample(range(1,50), 7))]
    m = min(ds); t = F(1, n*m)
    for _ in range(40):
        nt = move(ds, t)
        if nt == t: break
        big = nt + (nt - t)*3          # overshoot on purpose
        for j in range(1, 40):
            u = t + (big - t)*F(j,40)
            if all(circ(d*u) >= F(1,n) for d in ds): bad += 1; break
        t = nt
print(f"CONTROL, jumps deliberately 4x too far : {bad} caught (0 would mean the scan is blind)")
