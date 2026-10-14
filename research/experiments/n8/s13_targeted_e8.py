"""S13: targeted hunt in the CLEAN regime E_div == {8}.
There B_lit == B_hon on the windows (for b in W1, floor(8b/L) in {2,3}; for W2, in {4,5};
neither is in {0,7}), so every window fibre is admissible and the assumed framework
theorem is sound.  Question: can EVERY fibre in both windows be unsafe?
Mechanism to exploit: a rho=4 runner with e small blocks a whole parity class across a
whole window (e=12: t in {3,4} on W1 -> all odds; t in {7,8} on W2 -> all evens)."""
import sys, random
from math import gcd
from fractions import Fraction as F
from n8_fibre_core import L_of, split, safe, blocked_non, bad, t_of

def window_stats(E):
    L=L_of(E); Ed,En=split(E)
    if Ed!=[8]: return None
    W=[(-(-2*L//7),(2*L)//5),(-(-3*L//5),(5*L)//7)]
    n=s=0; ex=None
    for a,z in W:
        for b in range(a,z):
            n+=1
            if safe(En,b,L):
                s+=1
                if ex is None: ex=b
    return L,n,s,ex

def admissible(E):
    Ed,En=split(E)
    if Ed!=[8]: return False
    R=set(e%8 for e in En)
    if not ({1,3,5,7}<=R and len(R)==5): return False
    g=0
    for e in E: g=gcd(g,e)
    return g==1 and len(set(E))==7

# check the rho=4 parity-blocking claim for small e first
print("rho=4 runner: which e block a whole parity class throughout BOTH windows?")
good4=[]
for e in range(4,400,4):
    if e%8==0: continue                       # must be non-divisible: e = 4 mod 8
    ok=True; desc=[]
    for (lo,hi),wn in ((( F(2,7),F(2,5)),"W1"),((F(3,5),F(5,7)),"W2")):
        ts=set()
        # t = floor(e*x) for x in [lo,hi) : integer range
        t0=(e*lo.numerator)//lo.denominator
        t1=(e*(hi.numerator))//hi.denominator
        for t in range(t0,t1+1):
            if F(t,e)<hi and F(t+1,e)>lo: ts.add(t%8)
        if not ts<= {0,3,4,7}: ok=False; break
        desc.append(f"{wn}:t mod8 in {sorted(ts)}")
    if ok: good4.append((e,desc))
print("  e =", [e for e,_ in good4][:20])
for e,d in good4[:6]: print(f"    e={e}: {d}")
print()

random.seed(20260907)
best=[]
tested=0
cands4=[e for e,_ in good4] or [12]
for trial in range(400000):
    e4=random.choice(cands4)
    us={}
    for rho in (1,3,5,7):
        us[rho]=random.choice([rho+8*q for q in range(0,9)])
    tw_rho=random.choice([1,3,5,7])
    tw=random.choice([tw_rho+8*q for q in range(0,12)])
    E=tuple(sorted(set([8,e4,us[1],us[3],us[5],us[7],tw])))
    if len(E)!=7: continue
    if not admissible(E): continue
    if L_of(E)>400_000: continue
    tested+=1
    r=window_stats(E)
    if r is None: continue
    L,n,s,ex=r
    best.append((s/n if n else 1.0, s, n, E, L))
best.sort()
print(f"E_div=={{8}} configurations tested (randomised, L<=400000): {tested}")
print("lowest safe-fraction over the two windows:")
for frac,s,n,E,L in best[:15]:
    print(f"   E={E} L={L}  window fibres={n}  safe={s}  fraction={F(s,n)}")
zero=[x for x in best if x[1]==0]
print("configurations with ZERO safe window fibres:", len(zero))
for frac,s,n,E,L in zero[:10]:
    print("   ZERO:",E,"L=",L,"window fibres=",n)
