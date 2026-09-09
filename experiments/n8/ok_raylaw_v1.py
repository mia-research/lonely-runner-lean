r"""
ok_raylaw_v1 -- an exact closed form for EVERY ray sum?

Support-3 data suggested  R(p) = eps / (32 * prod|p_j|)  with eps = +-1.
Test across supports 2,3,4,5: compute R(p) numerically to high precision and look at
      C(p) := R(p) * prod_j |p_j|
to see whether C(p) takes finitely many values, and what determines it.
fhat(k) = -sin(pi k/4)/(pi k), fhat(k)=0 iff 4|k, so any p with a coordinate = 0 mod 4 has
R(p) = 0 and is skipped.
"""
from math import sin, pi, gcd
from fractions import Fraction as F
from functools import reduce
from itertools import product

def fhat(k):
    if k==0: return 0.75
    if k%4==0: return 0.0
    return -sin(pi*k/4)/(pi*k)

def ray(p, M=200000):
    s=0.0
    for m in range(1,M+1):
        t=1.0
        for x in p:
            t*=fhat(m*x)
            if t==0.0: break
        s+=t
    return 2*s

def prim(p): return reduce(gcd,[abs(x) for x in p])==1

print(f"{'support':>8} {'p':22} {'R(p)':>15} {'C = R*prod|p|':>16} {'as fraction':>12}")
rows=[]
for s in (2,3,4,5):
    seen=0
    for p in product(range(-5,6), repeat=s):
        if any(x==0 or x%4==0 for x in p): continue
        if not prim(p): continue
        if p[0]<0: continue
        R=ray(p)
        P=1
        for x in p: P*=abs(x)
        C=R*P
        fr=F(C).limit_denominator(4096)
        rows.append((s,p,R,C,fr))
        seen+=1
        if seen<=6:
            print(f"{s:>8} {str(p):22} {R:15.10f} {C:16.10f} {str(fr):>12}")
    vals=sorted({str(F(c).limit_denominator(4096)) for (ss,_,_,c,_) in rows if ss==s})
    print(f"   support {s}: {seen} primitive vectors tested, DISTINCT C values: {vals}\n")
