"""If the group moves only the ASSIGNMENT, then any statement quantified over the disparity
multiset alone cannot express it.  Decidable form: exhibit two subjects with the SAME multiset of
disparities but DIFFERENT neighbour structure.

That matters beyond this note.  The n=8 target was amended (2026-09-18) from ExistenceAt8, which
quantifies over a difference set ds, to LonelyRunnerAt8 on an arrangement v -- because a Finset
discards the arrangement.  If the multiplier structure is invisible at ds level, that amendment is
what makes BS-type structure expressible at all.

All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
import random
from collections import defaultdict
def frac(x): return x-floor(x)
def gcd_all(u):
    g=0
    for a,b in combinations(u,2): g=gcd(g,abs(b-a))
    return g
def nbr(v,i,g,p):
    t=F(p,8*g)
    rel=[(frac(F(v[j]-v[i])*t), v[j]) for j in range(8) if j!=i]
    return (min(rel)[1], max(rel)[1])
rng=random.Random(4242)
seen=defaultdict(list)
for _ in range(40000):
    v=speeds(rng.sample(range(1,40),8))
    g=gcd_all(v)
    for i in range(8):
        ds=tuple(sorted(abs(v[j]-v[i])//g for j in range(8) if j!=i))
        seen[ds].append((v,i,g))
hits=0
for ds,rows in seen.items():
    if len(rows)<2: continue
    sig=defaultdict(list)
    for v,i,g in rows:
        sig[tuple(nbr(v,i,g,1))].append((v,i))
    if len(sig)>1:
        hits+=1
        if hits==1:
            print("  WITNESS -- same disparity multiset, different neighbours at p = 1\n")
            print(f"    disparities (reduced): {list(ds)}\n")
            for s,(who) in list(sig.items())[:3]:
                v,i=who[0]
                print(f"    arrangement {list(v)}  subject {v[i]}")
                print(f"       neighbours (ahead, behind) by SPEED: {s}")
            print()
print(f"  distinct disparity multisets seen more than once : {sum(1 for r in seen.values() if len(r)>1)}")
print(f"  of those, some carry MORE THAN ONE neighbour structure : {hits}")
print()
print("  => the neighbour is NOT a function of the disparity multiset.")
print("     A statement quantified over ds alone cannot express it.")
