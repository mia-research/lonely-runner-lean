"""Is the flank at the SECOND-LARGEST difference always free?

Order 8: a subject has 7 differences. Flank e is free iff some opening k of e has every other
ratio clear: circDist((d/e)(k + 1/8)) >= 1/8 for all d != e. For integer differences the ratios
d/e have denominator dividing e, so the openings are periodic mod e and the check is finite.
"""
from fractions import Fraction as F
import random
TH = F(1,8)
def cd(x):
    f = x % 1; return min(f,1-f)
def free_openings(D, e):
    others = [d for d in D if d != e] if D.count(e)==1 else [d for i,d in enumerate(D) if i != D.index(e)]
    rs = [F(d,e) for d in others]
    return [k for k in range(e) if all(cd(r*(k+TH)) >= TH for r in rs)]
def which_flanks_free(D):
    return {e: free_openings(D,e) for e in sorted(set(D))}
rng = random.Random(11)
print("random integer difference sets of size 7 (order 8)")
print("checking: is the flank at the second-largest difference free?\n")
tot=0; sl_free=0; none_free=0; fails=[]
for trial in range(20000):
    Dmax = rng.randint(8, 60)
    D = sorted(rng.sample(range(1, Dmax), 6) + [Dmax])
    tot+=1
    ff = which_flanks_free(D)
    anyfree = [e for e,ks in ff.items() if ks]
    if not anyfree:
        none_free+=1; 
        if len(fails)<5: fails.append(D)
    sl = sorted(set(D))[-2] if len(set(D))>=2 else None
    if sl is not None and ff.get(sl): sl_free+=1
print(f"  sets tested: {tot}")
print(f"  second-largest flank free: {sl_free}  ({100*sl_free/tot:.1f}%)")
print(f"  NO flank free at all:      {none_free}")
if fails:
    print("  sets with no free flank (would refute Existence if real):")
    for D in fails: print("   ", D)
print()
print("largest flank free, for comparison:")
lf=0
rng2 = random.Random(11)
for trial in range(20000):
    Dmax = rng2.randint(8,60)
    D = sorted(rng2.sample(range(1,Dmax),6)+[Dmax])
    if free_openings(D, max(D)): lf+=1
print(f"  largest flank free: {lf} ({100*lf/20000:.1f}%)")
