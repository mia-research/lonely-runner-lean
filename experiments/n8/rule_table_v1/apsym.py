# Owner: the AP gives 4 global isolation events - two patterns and their inversions - and we
# only need ONE.  Check: (a) the 4 events are exactly the odd flanks' openings; (b) lonely_neg
# (t -> 1-t) pairs them; (c) does that pairing persist for general ds, across flanks?
from fractions import Fraction as F
from math import gcd
import random
def circ(x):
    f=x-(x.numerator//x.denominator); return min(f,1-f)
def lonely(ds,t): return all(circ(F(a)*t) >= F(1,8) for a in ds)
def openings(ds,b): return [(k, (F(8*k+1,8*b))) for k in range(b)]
ds=(1,2,3,4,5,6,7)
print("AP {1..7}: every flank's lonely openings, as instants")
ev=[]
for b in ds:
    L=[(k,t) for k,t in openings(ds,b) if lonely(ds,t)]
    if L: ev += [t for _,t in L]
    print(f"   flank {b} ({'odd ' if b%2 else 'even'}): " + (", ".join(f"k={k} t={t}" for k,t in L) if L else "none"))
print(f"   distinct isolation instants: {sorted(set(ev))}")
print(f"   count {len(set(ev))};  closed under t -> 1-t ? "
      f"{set(ev)=={F(1)-t for t in ev}}")
print()
# (c) general ds: is the set of lonely INSTANTS closed under t -> 1-t, and does it pair flanks?
rng=random.Random(3); ok=0; tot=0; crossflank=0
for _ in range(400):
    d=sorted(rng.sample(range(1,25),7)); g=gcd(*d); d=tuple(x//g for x in d)
    inst={}
    for b in d:
        for k,t in openings(d,b):
            if lonely(d,t): inst.setdefault(t,set()).add(b)
    if not inst: continue
    tot+=1
    S=set(inst)
    if S=={F(1)-t for t in S}: ok+=1
    # for each instant, is its mirror hosted by a DIFFERENT flank?
    for t,bs in inst.items():
        m=F(1)-t
        if m in inst and not (inst[m] & bs): crossflank+=1
print(f"general ds: {tot} sets with a lonely opening")
print(f"   lonely-instant set closed under t -> 1-t : {ok}/{tot}")
print(f"   mirrored instants hosted by a DIFFERENT flank: {crossflank} occurrences")
