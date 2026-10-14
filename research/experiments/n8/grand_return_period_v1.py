"""Grand return vs isolation period, and what periodicity gives the cascade.
Exact Fraction arithmetic. n=8, threshold 1/8.  2026-09-18."""
from fractions import Fraction as F
from math import gcd, floor, ceil
from itertools import combinations
import random, itertools

TH = F(1,8)
def circd(x):
    x = x - floor(x)
    return min(x, 1-x)
def inWay(d,t): return circd(d*t) < TH
def nextOpening(d,t):
    k = ceil(d*t - TH)
    if k < 0: k = 0
    while F(k,1)+TH < d*t: k += 1
    return (F(k,1)+TH)/d
def move(ds,t):
    b=[d for d in ds if inWay(d,t)]
    return t if not b else max(nextOpening(d,t) for d in b)
def disparities(v,i): return sorted(abs(v[j]-v[i]) for j in range(len(v)) if j!=i)
def G_of(v):
    g=0
    for a,b in combinations(v,2): g=gcd(g,abs(b-a))
    return g

print("="*72)
print("[1] isolation period P = 1/G : is inWay periodic with period P?")
random.seed(11)
bad=0; tested=0
for _ in range(300):
    v=sorted(random.sample(range(0,60),8))
    G=G_of(v); P=F(1,G)
    for i in range(8):
        ds=disparities(v,i)
        for d in ds:
            if (d*P).denominator != 1: bad+=1
            for _ in range(6):
                t=F(random.randint(0,4000),997)
                if inWay(d,t)!=inWay(d,t+P): bad+=1
                tested+=1
print(f"    300 arrangements, {tested} (d,t) checks : {bad} failures")

print("="*72)
print("[2] equivariance : move(t+P) == move(t)+P ?")
bad=0; tested=0
for _ in range(300):
    v=sorted(random.sample(range(0,60),8))
    G=G_of(v); P=F(1,G)
    for i in range(8):
        ds=disparities(v,i)
        for _ in range(4):
            t=F(random.randint(0,3000),733)
            if move(ds,t+P)!=move(ds,t)+P: bad+=1
            tested+=1
print(f"    {tested} checks : {bad} failures")

print("="*72)
print("[3] grand return  vs  isolation period  (they differ)")
for v in [(3,5),(1,2,3,4,5,6,7,8),(1,3,5,7,9,11,13,15),(2,4,6,8,10,12,14,16)]:
    g=0
    for s in v: g=gcd(g,s)
    G=G_of(v)
    print(f"    v={v}\n      grand return (all v_i t in Z) t=1/gcd(speeds) = 1/{g}"
          f"   |   isolation period 1/gcd(differences) = 1/{G}"
          f"   -> {'SAME' if g==G else 'DIFFER'}")

print("="*72)
print("[4] commensurable, not integer : does a period still exist?")
print("    speeds (1/2,3/2,5/2,...) : differences are integers -> period 1")
print("    speeds k*(1,2,...,8) for irrational k : disparities all multiples of k,")
print("      so t=1/k gives d*t in Z  -> a period EXISTS though speeds are irrational.")
print("    speeds (1, sqrt2) : need t with t, sqrt2*t both in Z -> sqrt2 rational. NO period.")
print("    => the condition is COMMENSURABILITY of the disparities, not integrality.")

print("="*72)
print("[5] does the cascade ever need to run past P ?  (exhaustive, small box)")
worst=None; over=0; n_inst=0; maxsteps=0
for v in itertools.combinations(range(0,15),8):
    if v[0]!=0: continue
    g=0
    for s in v[1:]: g=gcd(g,s)
    if g!=1: continue
    G=G_of(v); P=F(1,G)
    for i in range(8):
        ds=disparities(v,i); m=min(ds)
        t=F(1,8*m); steps=0
        while steps<4000:
            nt=move(ds,t)
            if nt==t: break
            t=nt; steps+=1
        n_inst+=1; maxsteps=max(maxsteps,steps)
        if t>P: over+=1
        r=t/P
        if worst is None or r>worst[0]: worst=(r,v,i,t,P,steps)
print(f"    runner-instances {n_inst}; cascade instant > P in {over} of them; max moves {maxsteps}")
print(f"    largest  t/P = {worst[0]}  at v={worst[1]} subject idx {worst[2]}"
      f"  (t={worst[3]}, P={worst[4]}, {worst[5]} moves)")

print("="*72)
print("[6] the step bound from periodicity : #distinct phases of openings mod P")
random.seed(7)
rows=[]
for _ in range(6):
    v=sorted(random.sample(range(0,80),8)); v=[x-v[0] for x in v]
    G=G_of(v); P=F(1,G)
    i=random.randrange(8); ds=disparities(v,i)
    bound=sum(d//G for d in ds)+1
    t=F(1,8*min(ds)); steps=0
    while steps<6000:
        nt=move(ds,t)
        if nt==t: break
        t=nt; steps+=1
    rows.append((v,i,G,bound,steps))
for v,i,G,b,s in rows:
    print(f"    G={G:3d}  phase bound sum(d/G)+1 = {b:6d}   actual moves = {s}")
