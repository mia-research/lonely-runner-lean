"""Can a difference set shadow the largest AND the second-largest flank at once?

If some designated PAIR of flanks can never both be shadowed, Existence closes: one of the two is
always free, and a free flank is a lonely opening (lonely_iff_exists_flank).
"""
from fractions import Fraction as F
import random
TH = F(1,8)
def cd(x):
    f = x % 1; return min(f,1-f)
def free_ks(D, e):
    rs = [F(d,e) for i,d in enumerate(D) if d != e or D.index(e)!=i]
    rs = [F(d,e) for d in D if d != e]
    return [k for k in range(e) if all(cd(r*(k+TH)) >= TH for r in rs)]
rng = random.Random(29)
both_shadowed = 0; tot = 0; minfree = 99; worst=None
dist = {}
for _ in range(40000):
    Dmax = rng.randint(8, 80)
    D = sorted(set(rng.sample(range(1, Dmax), 6) + [Dmax]))
    if len(D) != 7: continue
    tot += 1
    freeflanks = [e for e in D if free_ks(D, e)]
    nf = len(freeflanks)
    dist[nf] = dist.get(nf, 0) + 1
    if nf < minfree: minfree = nf; worst = (D, freeflanks)
    e1, e2 = D[-1], D[-2]
    if not free_ks(D, e1) and not free_ks(D, e2): both_shadowed += 1
print(f"sets tested: {tot}")
print(f"largest AND second-largest both shadowed: {both_shadowed}")
print(f"distribution of how many of the 7 flanks are free: {dict(sorted(dist.items()))}")
print(f"fewest free flanks seen: {minfree}   example {worst[0]} -> free flanks {worst[1]}")
