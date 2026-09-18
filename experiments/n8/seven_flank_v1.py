"""How close does an arrangement get to having ALL SEVEN flanks of one runner shadowed?
A runner with all seven shadowed has NO lonely instant (Cor 6.4), which would refute LRC(8) --
a theorem (Rosenfeld 2025).  So this measures the MARGIN, not the outcome.

Exactness: Thm 6.13 (circDist_periodic_of_int_flank) -- at a whole-number flank e the verdict
repeats with period e, so k = 0..e-1 carries every verdict.  For integer disparity sets this makes
'flank e is shadowed' DECIDABLE, not sampled."""
import random, time
from fractions import Fraction as F
from math import floor, gcd
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def flank_shadowed(ds,e):
    """exact: verdict at an integer flank repeats with period e"""
    for k in range(e):
        t=(F(k)+TH)/F(e)
        if all(circd(F(d)*t)>=TH for d in ds): return False
    return True
def n_shadowed(ds): return sum(1 for e in ds if flank_shadowed(ds,e))

print("=== A. the recorded one-free-flank family {2,...,7,16} ===")
ds=[2,3,4,5,6,7,16]
print(f"   ds = {ds}   shadowed flanks: {n_shadowed(ds)} of 7")
print(f"   free flanks: {[e for e in ds if not flank_shadowed(ds,e)]}")
for m in [1,2,3]:
    d=[2,3,4,5,6,7,16*m]
    print(f"   {d}: shadowed {n_shadowed(d)} of 7   free {[e for e in d if not flank_shadowed(d,e)]}")

print()
print("=== B. exhaustive-ish: every 7-subset of [1,16] with gcd 1 ===")
from itertools import combinations
hist={}
best=(0,None)
for ds in combinations(range(1,17),7):
    g=0
    for d in ds: g=gcd(g,d)
    if g!=1: continue
    s=n_shadowed(list(ds))
    hist[s]=hist.get(s,0)+1
    if s>best[0]: best=(s,ds)
print(f"   distribution of shadowed-flank counts: {dict(sorted(hist.items()))}")
print(f"   maximum: {best[0]} of 7   at ds = {best[1]}")

print()
print("=== C. adversarial hill-climb, maximise shadowed flanks ===")
rng=random.Random(918); t0=time.time(); BEST=(0,None)
while time.time()-t0<120:
    ds=sorted(rng.sample(range(1,60),7))
    cur=n_shadowed(ds)
    for _ in range(300):
        if time.time()-t0>120: break
        cand=list(ds); i=rng.randrange(7)
        cand[i]=max(1,cand[i]+rng.choice([-3,-2,-1,1,2,3]))
        cand=sorted(set(cand))
        if len(cand)!=7: continue
        g=0
        for d in cand: g=gcd(g,d)
        if g!=1: continue
        s=n_shadowed(cand)
        if s>=cur:
            ds,cur=cand,s
            if s>BEST[0]:
                BEST=(s,tuple(ds)); print(f"   {s} of 7 shadowed at ds = {tuple(ds)}  (t+{time.time()-t0:.0f}s)")
print(f"   BEST: {BEST[0]} of 7 shadowed   ds = {BEST[1]}")
if BEST[1]:
    free=[e for e in BEST[1] if not flank_shadowed(list(BEST[1]),e)]
    print(f"   free flanks: {free}")
    for e in free:
        ks=[k for k in range(e) if all(circd(F(d)*((F(k)+TH)/F(e)))>=TH for d in BEST[1])]
        print(f"      flank {e}: clear at openings k = {ks[:12]}{'...' if len(ks)>12 else ''}  ({len(ks)} of {e})")
