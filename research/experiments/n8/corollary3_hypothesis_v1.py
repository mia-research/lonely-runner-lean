"""Does BS Corollary 3's HYPOTHESIS hold at order 8?

Careful about the object.  A parallel session measured slot multiplicity -- runners sharing
u_i mod 8.  Corollary 3's hypothesis is about something else: the 2-adic LEVELS of the DISPARITY
set,  D(j) = { d in ds : nu_2(d) = j },  and it needs  |D(j)| <= 3  for every j below the top.

(The two are linked -- two runners share a residue iff their disparity has nu >= 3 -- but they are
not the same partition, and conflating them would answer the wrong question.)

Measured on the same primitive sweep the other session used, speeds 1..17.  All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from math import gcd
from itertools import combinations
from collections import Counter
def gcd_all(u):
    g=0
    for a,b in combinations(u,2): g=gcd(g,abs(b-a))
    return g
def nu2(d):
    k=0
    while d%2==0: d//=2; k+=1
    return k
tot=0; ok=0; lvl0=Counter(); worst=Counter()
for w in combinations(range(1,17),7):
    v=speeds((1,)+tuple(x+1 for x in w))
    if gcd_all(v)!=1: continue
    for i in range(8):
        ds=[abs(v[j]-v[i]) for j in range(8) if j!=i]
        lv=Counter(nu2(d) for d in ds)
        m=max(lv)                                  # top level
        below=[c for j,c in lv.items() if j<m]
        tot+=1
        lvl0[lv[0]]+=1
        worst[max(below) if below else 0]+=1
        if all(c<=3 for c in below): ok+=1
print(f"  {tot} primitive subject-instances (speeds 1..17)\n")
print(f"  Corollary 3 hypothesis holds (every level below top has <= 3): {ok}  ({ok/tot:.4f})")
print(f"\n  largest level below the top: {dict(sorted(worst.items()))}")
print(f"  size of level nu=0 (odd disparities): {dict(sorted(lvl0.items()))}")
print()
print("  For comparison, the SLOT statistic the other session measured is a different partition;")
print("  its true bound is 7 (slot_multiplicity_v1.py), not the 3 their v<=16 sweep suggested.")
