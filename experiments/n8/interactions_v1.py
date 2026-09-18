"""Downhill consequences of this session's theorems, and their interactions.

(A) near_block_host_large x clear_iff.
    At scale d_min (N=0, host c), a COLLIDING disparity a = 8b reads s = 8b/c and fails iff
    r = b mod c is in an end zone.  near_block_host_large says a near failure needs c > 8.
    CONSEQUENCE: if c = d_min/g <= 8, every colliding failure at d_min is EXACT -- the disparity
    is an exact multiple of 8.d_min and the runner is exactly ON the subject.

(B) clear_iff is the k = 0 rung of a stratification by depth.  Is there a k = 1 rung?
    Depth <= 1 means clear at d_min, or clear after the single forced move.  The move is
    t' = max over blockers of nextOp, so depth <= 1 is decidable in closed form.  Question is
    whether it is CLEAN -- i.e. expressible as a residue condition like the k = 0 rung.
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
import random
from collections import Counter
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def gcd_all(u):
    g=0
    for a,b in combinations(u,2): g=gcd(g,abs(b-a))
    return g
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def depth(ds):
    t=TH/min(ds); n=0
    while n<4000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return n
        t=max(nextOp(d,t) for d in b); n+=1
    return None

print("=== (A) c <= 8  =>  every colliding failure at d_min is EXACT ===")
rng=random.Random(4321); viol=0; tested=0; exact=0; near=0
for _ in range(4000):
    v=speeds(rng.sample(range(1,90),8))
    g=gcd_all(v)
    for i in range(8):
        ds=[abs(v[j]-v[i])//g for j in range(8) if j!=i]
        c=min(ds)
        for a in ds:
            if a%8: continue                              # colliding only
            b=a//8
            fails = not (c <= a%(8*c) <= 7*c)
            if not fails: continue
            tested+=1
            is_exact = (b % c == 0)
            exact+=is_exact; near+= (not is_exact)
            if c<=8 and not is_exact: viol+=1
print(f"    colliding failures at d_min : {tested}   exact {exact}  near {near}")
print(f"    VIOLATIONS of 'c <= 8 => exact' : {viol}")

print("\n=== (B) the k = 1 rung ===")
rng=random.Random(777)
dist=Counter(); k1_c=Counter()
for _ in range(3000):
    v=speeds(rng.sample(range(1,90),8))
    g=gcd_all(v)
    for i in range(8):
        ds=[F(abs(v[j]-v[i])) for j in range(8) if j!=i]
        d=depth(ds)
        if d is None: continue
        dist[min(d,6)]+=1
        if d==1:
            c=int(min(ds))//g
            k1_c[min(c,12)]+=1
print(f"    depth distribution (capped at 6): {dict(sorted(dist.items()))}")
print(f"    depth == 1: c = d_min/g distribution: {dict(sorted(k1_c.items()))}")
tot=sum(dist.values())
print(f"    depth 0: {dist[0]/tot:.4f}   depth 1: {dist[1]/tot:.4f}   depth >=2: {1-(dist[0]+dist[1])/tot:.4f}")
print("\n    k=1 is reachable in closed form (the move is forced once the blockers are known),")
print("    but whether it reduces to a residue band like k=0 is the open part.")
