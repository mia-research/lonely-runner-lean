"""Owner: "does the variation away from AP/grid change the neighbour of the isolation in a
predictable way?"

CANDIDATE RULE.  At t = p/(n g) runner j sits at (pi(j) - pi(i)) p / n relative to subject i, so
the neighbour AHEAD is the runner with  pi(j) - pi(i) = p  (mod 8)  and BEHIND with  = -p.
(pi = residue of the reduced speed; p^-1 = p because (Z/8)^x is Klein.)

Combined with the residue partition, this predicts:
  subject's residue UNIQUE -> lonely at t = 1/(8g), 0 cascade moves,
                              neighbours at residue difference +-1
  subject's residue SHARED -> no grid instant survives, the cascade moves, rule does not apply.
All speeds positive (_frame guard)."""
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
def frac(x): return x-floor(x)
def reduced(v):
    g=0
    for a,b in combinations(v,2): g=gcd(g,abs(b-a))
    return [(x-min(v))//g for x in v], g
def neighbours(v,i,t):
    sep=[(frac(F(v[j]-v[i])*t), j) for j in range(8) if j!=i]
    return min(sep)[1], max(sep)[1]
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def cascade(ds):
    m=min(ds); t=TH/m; n=0
    while n<4000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return t,n
        t=max(nextOp(d,t) for d in b); n+=1
    return None,0

print("=== 1. on GRIDS: is the neighbour at instant p the runner at residue difference +-p? ===")
rng=random.Random(7); ok=0; tot=0
tested=0
while tested<400:
    v=speeds(rng.sample(range(1,40),8))
    u,g=reduced(v); res=[x%8 for x in u]
    if len(set(res))!=8: continue
    tested+=1
    for i in range(8):
        for p in (1,3,5,7):
            a,b=neighbours(v,i,F(p,8*g))
            tot+=1
            if (res[a]-res[i])%8==p%8 and (res[b]-res[i])%8==(-p)%8: ok+=1
print(f"   {ok} of {tot} agree   ({ok/tot:.6f})   over {tested} grids")

print()
print("=== 2. on GENERAL arrangements: does the residue partition predict the cascade? ===")
rng=random.Random(19)
uniq=Counter(); shar=Counter(); nb_ok=0; nb_tot=0
for _ in range(3000):
    v=speeds(rng.sample(range(1,90),8))
    u,g=reduced(v); res=[x%8 for x in u]; c=Counter(res)
    for i in range(8):
        ds=sorted(F(abs(v[j]-v[i])) for j in range(8) if j!=i)
        t,n=cascade(ds)
        if t is None: continue
        unique = c[res[i]]==1
        if unique:
            uniq['n']+=1
            uniq['stops at 1/(8g)'] += 1 if t==F(1,8*g) else 0
            uniq['zero moves'] += 1 if n==0 else 0
            a,b=neighbours(v,i,t); nb_tot+=1
            if (res[a]-res[i])%8==1 and (res[b]-res[i])%8==7: nb_ok+=1; uniq['neighbours +-1']+=1
        else:
            shar['n']+=1
            shar['zero moves'] += 1 if n==0 else 0
print(f"   UNIQUE residue: {uniq['n']} subjects")
print(f"      cascade stops at t = 1/(8g) : {uniq['stops at 1/(8g)']/uniq['n']:.4f}")
print(f"      zero cascade moves          : {uniq['zero moves']/uniq['n']:.4f}")
print(f"      neighbours at residue diff +-1 : {uniq['neighbours +-1']/uniq['n']:.4f}")
print(f"   SHARED residue: {shar['n']} subjects")
print(f"      zero cascade moves          : {shar['zero moves']/shar['n']:.4f}")
